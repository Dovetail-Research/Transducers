import Transducers.Traj
import Transducers.AnticipationFree

/-!
# Interfaces

An *interface* describes, at every time `n : ℕ`, the law of the observation at time `n` given
the actions at times `0, …, n` and the observations at times `0, …, n - 1`.

Using Mathlib's Ionescu-Tulcea construction `ProbabilityTheory.Kernel.traj`, an interface yields
a joint law of the whole observation sequence given the whole action sequence, which is
anticipation-free.

To run `Kernel.traj`, coordinate `n` of the trajectory holds the full action sequence together
with the observations at times `0, …, n - 1`.

## Main results

* `Interface.obsKernel`: the joint law of the observations given the actions.
* `Interface.eq_obsKernel`: a kernel equals `obsKernel` as soon as its finite-horizon marginals
  are built step by step from the interface.
* `Interface.anticipationFree_obsKernel`: `obsKernel` is anticipation-free.
-/

open MeasureTheory ProbabilityTheory Finset Preorder ProbabilityTheory.Kernel

noncomputable section

variable {A O : Type} [MeasurableSpace A] [MeasurableSpace O]

/-- An interface: at time `n`, the observation is drawn given the actions at times `0, …, n` and
the observations at times `0, …, n - 1`. -/
structure Interface (A O : Type) [MeasurableSpace A] [MeasurableSpace O] where
  κ : (n : ℕ) → MarkovKernel ((Fin (n + 1) → A) × (Fin n → O)) O

/-- Restrict a sequence to its first `n` entries. -/
def restrictFin {β : Type} (n : ℕ) (x : ℕ → β) : Fin n → β := fun i ↦ x i

@[fun_prop]
lemma measurable_restrictFin {β : Type} [MeasurableSpace β] (n : ℕ) :
    Measurable (restrictFin (β := β) n) := by
  unfold restrictFin
  fun_prop

lemma measurable_fin_snoc {n : ℕ} :
    Measurable (fun q : (Fin n → O) × O ↦ (Fin.snoc q.1 q.2 : Fin (n + 1) → O)) :=
  Measurable.of_eval fun i ↦ by
    induction i using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; exact measurable_snd
    | cast i => simp only [Fin.snoc_castSucc]; exact (measurable_pi_apply i).comp measurable_fst

namespace Interface

variable (I : Interface A O)

/-- One step of the trajectory: keep the action sequence, and append an observation drawn from
the interface given the first `n + 1` actions and the `n` observations so far. -/
def step (n : ℕ) :
    Kernel (Π i : Iic n, (ℕ → A) × (Fin i → O)) ((ℕ → A) × (Fin (n + 1) → O)) :=
  ((Kernel.id ×ₖ (I.κ n).1.comap (fun p : (ℕ → A) × (Fin n → O) ↦ (restrictFin (n + 1) p.1, p.2))
      (by fun_prop)).map (fun q ↦ (q.1.1, Fin.snoc q.1.2 q.2))).comap
    (fun z ↦ z ⟨n, mem_Iic.2 le_rfl⟩) (by fun_prop)

instance (n : ℕ) : IsMarkovKernel (I.step n) := by
  unfold step
  have : IsMarkovKernel ((Kernel.id ×ₖ (I.κ n).1.comap
      (fun p : (ℕ → A) × (Fin n → O) ↦ (restrictFin (n + 1) p.1, p.2)) (by fun_prop)).map
      (fun q ↦ (q.1.1, Fin.snoc q.1.2 q.2) : _ → (ℕ → A) × (Fin (n + 1) → O))) :=
    IsMarkovKernel.map _ (measurable_fst.fst.prodMk
      (measurable_fin_snoc.comp (measurable_fst.snd.prodMk measurable_snd)))
  infer_instance

/-! ### The observation kernel -/

/-- The starting point of the trajectory: the action sequence, with no observations yet. -/
def start (a : ℕ → A) : Π i : Iic 0, (ℕ → A) × (Fin i → O) :=
  fun i ↦ (a, fun j ↦ absurd (j.2.trans_le (mem_Iic.1 i.2)) j.val.not_lt_zero)

@[fun_prop]
lemma measurable_start : Measurable (start (A := A) (O := O)) := by
  unfold start
  fun_prop

/-- The joint law of the observations given the actions: run `Kernel.traj` from the action
sequence, and read the observation at time `n` off the last entry of coordinate `n + 1`. -/
def obsKernel : Kernel (ℕ → A) (ℕ → O) :=
  ((traj I.step 0).comap start measurable_start).map
    (fun (ω : Π n, (ℕ → A) × (Fin n → O)) n ↦ (ω (n + 1)).2 (Fin.last n))

instance : IsMarkovKernel I.obsKernel :=
  IsMarkovKernel.map _ (by fun_prop)

/-- The observations of `obsKernel` up to time `d` only depend on the actions up to time `d`. -/
lemma obsKernel_map_restrictIic (d : ℕ) (x y : ℕ → A) (hxy : ∀ e ≤ d, x e = y e) :
    (I.obsKernel x).map (restrictIic d) = (I.obsKernel y).map (restrictIic d) := by
  -- Overwrite the actions after time `d` by those of `y`.
  let τ : (ℕ → A) → (ℕ → A) := fun b i ↦ if i ≤ d then b i else y i
  have hτ : Measurable τ := Measurable.of_eval fun i ↦ by
    by_cases hi : i ≤ d
    · simpa [τ, hi] using measurable_pi_apply i
    · simp [τ, hi]
  let F : (n : ℕ) → (ℕ → A) × (Fin n → O) → (ℕ → A) × (Fin n → O) := fun _ ↦ Prod.map τ id
  have hF : ∀ n, Measurable (F n) := fun _ ↦ hτ.prodMap measurable_id
  -- The step kernels up to time `d` commute with `F`.
  have hstep : ∀ n < d + 1, (I.step n).comap (coordMap F) (measurable_coordMap hF) =
      (I.step n).map (F (n + 1)) := by
    intro n hn
    -- `step n` is a kernel `core` on the current coordinate, pulled back along `top`.
    have hP : Measurable (Prod.map τ (id : (Fin n → O) → (Fin n → O))) :=
      hτ.prodMap measurable_id
    have hP' : Measurable (Prod.map τ (id : (Fin (n + 1) → O) → (Fin (n + 1) → O))) :=
      hτ.prodMap measurable_id
    have hg : Measurable (fun q : ((ℕ → A) × (Fin n → O)) × O ↦
        ((q.1.1, Fin.snoc q.1.2 q.2) : (ℕ → A) × (Fin (n + 1) → O))) :=
      measurable_fst.fst.prodMk
        (measurable_fin_snoc.comp (measurable_fst.snd.prodMk measurable_snd))
    have hinp : ((I.κ n).1.comap
        (fun p : (ℕ → A) × (Fin n → O) ↦ (restrictFin (n + 1) p.1, p.2)) (by fun_prop)).comap
          (Prod.map τ id) hP = (I.κ n).1.comap
        (fun p : (ℕ → A) × (Fin n → O) ↦ (restrictFin (n + 1) p.1, p.2)) (by fun_prop) := by
      ext1 p
      have hr : restrictFin (n + 1) (τ p.1) = restrictFin (n + 1) p.1 :=
        funext fun i ↦ by simp [restrictFin, τ, show (i : ℕ) ≤ d by lia]
      simp only [comap_apply, Prod.map_fst, Prod.map_snd, id_eq, hr]
    -- The step only reads the first `n + 1 ≤ d + 1` actions, which `τ` does not change.
    have hcore : ((Kernel.id ×ₖ (I.κ n).1.comap
        (fun p : (ℕ → A) × (Fin n → O) ↦ (restrictFin (n + 1) p.1, p.2)) (by fun_prop)).map
          (fun q ↦ ((q.1.1, Fin.snoc q.1.2 q.2) : (ℕ → A) × (Fin (n + 1) → O)))).comap
          (Prod.map τ id) hP =
        ((Kernel.id ×ₖ (I.κ n).1.comap
        (fun p : (ℕ → A) × (Fin n → O) ↦ (restrictFin (n + 1) p.1, p.2)) (by fun_prop)).map
          (fun q ↦ ((q.1.1, Fin.snoc q.1.2 q.2) : (ℕ → A) × (Fin (n + 1) → O)))).map
          (Prod.map τ id) := by
      rw [comap_map_comm _ _ hg, comap_prod, hinp, id_comap, ← id_map hP, map_prod_eq _ _ hP,
        ← map_comp_right _ (hP.prodMap measurable_id) hg, ← map_comp_right _ hg hP']
      rfl
    have lift : ∀ K : Kernel ((ℕ → A) × (Fin n → O)) ((ℕ → A) × (Fin (n + 1) → O)),
        K.comap (Prod.map τ id) hP = K.map (Prod.map τ id) →
        (K.comap (fun z : Π i : Iic n, (ℕ → A) × (Fin i → O) ↦ z ⟨n, mem_Iic.2 le_rfl⟩)
          (by fun_prop)).comap (coordMap F) (measurable_coordMap hF) =
        (K.comap (fun z : Π i : Iic n, (ℕ → A) × (Fin i → O) ↦ z ⟨n, mem_Iic.2 le_rfl⟩)
          (by fun_prop)).map (Prod.map τ id) := by
      intro K hK
      rw [← comap_map_comm _ _ hP', ← hK]
      rfl
    exact lift _ hcore
  -- After applying `F`, the starting point of `x` becomes that of `y`.
  have hstart : coordMap F (start (O := O) x) = start y := by
    funext i
    simp only [coordMap, F, start, Prod.map, id_eq, Prod.mk.injEq, and_true]
    funext n
    by_cases hn : n ≤ d
    · simp [τ, hn, hxy n hn]
    · simp [τ, hn]
  -- The observations up to time `d` are read off the trajectory up to time `d + 1`.
  let G : (Π i : Iic (d + 1), (ℕ → A) × (Fin i → O)) → Set.Iic d → O :=
    fun w e ↦ (w ⟨e + 1, mem_Iic.2 (by have := e.2; simp only [Set.mem_Iic] at this; lia)⟩).2
      (Fin.last e)
  have hG : Measurable G := by unfold G; fun_prop
  have key : ∀ z : ℕ → A, (I.obsKernel z).map (restrictIic d) =
      ((traj I.step 0 (start z)).map
        (frestrictLe (π := fun i ↦ (ℕ → A) × (Fin i → O)) (d + 1))).map G := by
    intro z
    rw [obsKernel, map_apply _ (by fun_prop), comap_apply,
      Measure.map_map (measurable_restrictIic d) (by fun_prop),
      Measure.map_map hG (measurable_frestrictLe _)]
    rfl
  rw [key, key, ← hstart, traj_map_frestrictLe_coordMap hF (d + 1) hstep,
    Measure.map_map hG (measurable_coordMap hF)]
  rfl

/-- The trajectory up to time `m`, laid out from the action sequence `a` and the first `m`
observations `w`. -/
def layout (m : ℕ) (a : ℕ → A) (w : Fin m → O) : Π i : Iic m, (ℕ → A) × (Fin i → O) :=
  fun i ↦ (a, fun j ↦ w (Fin.castLE (mem_Iic.1 i.2) j))

lemma measurable_layout (m : ℕ) (a : ℕ → A) : Measurable (layout (O := O) m a) := by
  unfold layout
  fun_prop

/-- One step of `partialTraj`, started from a laid-out trajectory. -/
lemma partialTraj_succ_self_layout (b : ℕ) (a : ℕ → A) (w : Fin b → O) :
    partialTraj (X := fun n ↦ (ℕ → A) × (Fin n → O)) I.step b (b + 1) (layout b a w) =
      ((I.κ b).1 (restrictFin (b + 1) a, w)).map (fun o ↦ layout (b + 1) a (Fin.snoc w o)) := by
  have h4 : Measurable (fun q : ((ℕ → A) × (Fin b → O)) × O ↦
      ((q.1.1, Fin.snoc q.1.2 q.2) : (ℕ → A) × (Fin (b + 1) → O))) :=
    measurable_fst.fst.prodMk (measurable_fin_snoc.comp (measurable_fst.snd.prodMk measurable_snd))
  rw [partialTraj_succ_self, Kernel.map_apply _ (by exact measurable_IicProdIoc), Kernel.prod_apply,
    Kernel.id_apply, Measure.dirac_prod, Kernel.map_apply _ (MeasurableEquiv.measurable _),
    step, comap_apply, Kernel.map_apply _ h4, Kernel.prod_apply, Kernel.id_apply,
    Measure.dirac_prod, comap_apply]
  have h1 : Measurable (IicProdIoc (X := fun n ↦ (ℕ → A) × (Fin n → O)) b (b + 1)) :=
    measurable_IicProdIoc
  rw [Measure.map_map h1 measurable_prodMk_left,
    Measure.map_map (h1.comp measurable_prodMk_left) (MeasurableEquiv.measurable _),
    Measure.map_map ((h1.comp measurable_prodMk_left).comp (MeasurableEquiv.measurable _)) h4,
    Measure.map_map (((h1.comp measurable_prodMk_left).comp (MeasurableEquiv.measurable _)).comp
      h4) measurable_prodMk_left]
  congr 1
  funext o i
  obtain ⟨i, hi⟩ := i
  by_cases h : i ≤ b
  · simp only [Function.comp_apply, IicProdIoc, h, dite_true, layout, Prod.mk.injEq, true_and]
    funext j
    have hj : (j : ℕ) < b := lt_of_lt_of_le j.2 h
    simp [Fin.snoc, hj]
    rfl
  · obtain rfl : i = b + 1 := by simp only [mem_Iic] at hi; lia
    simp only [Function.comp_apply, IicProdIoc, h, dite_false]
    rfl

/-- **Characterization of `obsKernel`.** A kernel `ν` from action sequences to observation
sequences equals `I.obsKernel` as soon as, for every `n`, its law of the first `n + 1` observations
is obtained from its law of the first `n` observations by drawing the next observation from the
interface. -/
theorem eq_obsKernel (ν : Kernel (ℕ → A) (ℕ → O)) [IsMarkovKernel ν]
    (h : ∀ n a, (ν a).map (restrictFin (n + 1)) =
      ((ν a).map (restrictFin n) ⊗ₘ (I.κ n).1.comap (fun w ↦ (restrictFin (n + 1) a, w))
        (by fun_prop)).map (fun p ↦ Fin.snoc p.1 p.2)) :
    I.obsKernel = ν := by
  -- The candidate trajectory kernel: lay out the actions and the observations drawn from `ν`.
  let e : (Π i : Iic 0, (ℕ → A) × (Fin i → O)) → (ℕ → A) := fun z ↦ (z ⟨0, mem_Iic.2 le_rfl⟩).1
  have he : Measurable e := by fun_prop
  let η : Kernel (Π i : Iic 0, (ℕ → A) × (Fin i → O)) (Π n, (ℕ → A) × (Fin n → O)) :=
    (Kernel.id ×ₖ ν.comap e he).map (fun p n ↦ (e p.1, restrictFin n p.2))
  have hη : ∀ z, η z = (ν (e z)).map (fun y n ↦ (e z, restrictFin n y)) := by
    intro z
    rw [Kernel.map_apply _ (by fun_prop), Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
      comap_apply, Measure.map_map (by fun_prop) measurable_prodMk_left]
    rfl
  have hm : ∀ b z, (η.map (frestrictLe b)) z =
      ((ν (e z)).map (restrictFin b)).map (layout b (e z)) := by
    intro b z
    rw [Kernel.map_apply _ (measurable_frestrictLe b), hη,
      Measure.map_map (measurable_frestrictLe b) (by fun_prop),
      Measure.map_map (measurable_layout _ _) (measurable_restrictFin _)]
    rfl
  have htraj : η = traj (X := fun n ↦ (ℕ → A) × (Fin n → O)) I.step 0 := by
    refine eq_traj (X := fun n ↦ (ℕ → A) × (Fin n → O)) I.step η fun b ↦ ?_
    induction b with
    | zero =>
      rw [partialTraj_self]
      ext1 z
      rw [hm, Kernel.id_apply]
      have : layout 0 (e z) = fun _ ↦ z := by
        funext w i
        obtain ⟨i, hi⟩ := i
        obtain rfl : i = 0 := by simpa using hi
        exact Prod.ext rfl (funext fun j ↦ j.elim0)
      rw [this, Measure.map_const, measure_univ, one_smul]
    | succ b ih =>
      rw [partialTraj_succ_eq_comp (Nat.zero_le b), ← ih]
      ext1 z
      rw [Kernel.comp_apply, hm, hm, Measure.bind_map (measurable_layout _ _).aemeasurable
        (Kernel.measurable _).aemeasurable, h b, Measure.map_map (measurable_layout _ _)
        (measurable_fin_snoc), Measure.compProd_eq_comp_prod,
        Measure.map_comp _ _ ((measurable_layout _ _).comp measurable_fin_snoc)]
      congr 1
      funext w
      symm
      rw [partialTraj_succ_self_layout, Kernel.map_apply _
        ((measurable_layout _ _).comp measurable_fin_snoc), Kernel.prod_apply, Kernel.id_apply,
        Measure.dirac_prod, comap_apply, Measure.map_map
        ((measurable_layout _ _).comp measurable_fin_snoc) measurable_prodMk_left]
      rfl
  ext1 a
  rw [obsKernel, Kernel.map_apply _ (by fun_prop), comap_apply, ← htraj, hη,
    Measure.map_map (by fun_prop) (by fun_prop)]
  conv_rhs => rw [← Measure.map_id (μ := ν a)]
  rfl

/-- The observation kernel of an interface is anticipation-free. -/
theorem anticipationFree_obsKernel : I.obsKernel.AnticipationFree :=
  fun d x y hxy ↦ I.obsKernel_map_restrictIic d x y fun e he ↦ congrFun hxy ⟨e, he⟩

end Interface
