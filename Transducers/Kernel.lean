import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Kernels

Helpers for Markov kernels, restrictions of `T`-indexed families to the past and future of an
index (and gluing them back together), two lemmas on maps of kernels and composition-products,
and the causal-Markov property of a kernel.
-/

open MeasureTheory ProbabilityTheory

universe u_1 u_2 u_3

noncomputable section

-- This abbreviation is here so that instead of typing
---- `Subtype (@ProbabilityTheory.IsMarkovKernel α β mα mβ)`
-- we can just type
---- `MarkovKernel α β`
abbrev MarkovKernel (α : Type u_1) (β : Type u_2) [mα : MeasurableSpace α]
  [mβ : MeasurableSpace β] := Subtype (IsMarkovKernel (mα := mα) (mβ := mβ))

-- This instance registration tells allows us to know that mapping a MarkovKernel by a
-- MeasurableEquiv is still a MarkovKernel
instance {α : Type u_1} {β : Type u_2} {γ : Type u_3} [MeasurableSpace α] [MeasurableSpace β]
      [MeasurableSpace γ] {k : Kernel α β} [IsMarkovKernel k] (f : MeasurableEquiv β γ) :
    IsMarkovKernel (k.map f) := Kernel.IsMarkovKernel.map _ (MeasurableEquiv.measurable _)

-- This instance registration tells allows us to know that comapping a MarkovKernel by a
-- MeasurableEquiv is still a MarkovKernel
instance {α : Type u_1} {β : Type u_2} {γ : Type u_3} [MeasurableSpace α] [MeasurableSpace β]
      [MeasurableSpace γ] {k : Kernel α β} [IsMarkovKernel k] (f : MeasurableEquiv γ α) :
    IsMarkovKernel (k.comap f (f.measurable)) :=
  Kernel.IsMarkovKernel.comap _ (MeasurableEquiv.measurable _)

-- This instance registration tells Lean's typeclass search that if it is holding an object of type
-- `MarkovKernel` then it can find a proof of its markovianness by calling `k.2`.
instance {α : Type u_1} {β : Type u_2} [MeasurableSpace α]
  [MeasurableSpace β] (k : MarkovKernel α β) : ProbabilityTheory.IsMarkovKernel k.1 := k.2

-- This instance registration tells Lean's typeclass search that if someone tries call the
-- `MarkovKernel` as if it's a function, then Lean should reroute that call by calling `f.1`.
instance {α : Type u_1} {β : Type u_2} [MeasurableSpace α]
  [MeasurableSpace β] : CoeFun (MarkovKernel α β) (fun _ ↦ α → Measure β) := ⟨
    fun f ↦ ⇑f.1
  ⟩

-- This instance lets us use Kernels in place of MarkovKernels in places where Lean can
-- synthesise its markovianness
instance {α : Type u_1} {β : Type u_2} [MeasurableSpace α] [MeasurableSpace β]
  {k : Kernel α β} [hk : IsMarkovKernel k] : CoeDep (Kernel α β) k (MarkovKernel α β) := ⟨
    ⟨k, hk⟩
  ⟩

/-- Restrict a `T`-indexed family to the indices `e ≤ d`. -/
def restrictIic {T β : Type} [Preorder T] (d : T) (x : T → β) : Set.Iic d → β :=
  fun e ↦ x e

/-- Restrict a `T`-indexed family to the indices `e > d`. -/
def restrictIoi {T β : Type} [Preorder T] (d : T) (x : T → β) : Set.Ioi d → β :=
  fun e ↦ x e

@[fun_prop]
lemma measurable_restrictIic {T β : Type} [Preorder T] [MeasurableSpace β] (d : T) :
    Measurable (restrictIic (β := β) d) := by
  unfold restrictIic
  fun_prop

@[fun_prop]
lemma measurable_restrictIoi {T β : Type} [Preorder T] [MeasurableSpace β] (d : T) :
    Measurable (restrictIoi (β := β) d) := by
  unfold restrictIoi
  fun_prop

/-- Split a `T`-indexed family at `d` into its past (indices `≤ d`) and its future
(indices `> d`). -/
def splitIicIoi {T β : Type} [LinearOrder T] [MeasurableSpace β] (d : T) :
    (T → β) ≃ᵐ (Set.Iic d → β) × (Set.Ioi d → β) where
  toFun y := (restrictIic d y, restrictIoi d y)
  invFun p e := if h : e ≤ d then p.1 ⟨e, h⟩ else p.2 ⟨e, not_le.1 h⟩
  left_inv y := funext fun e ↦ by
    simp only [restrictIic, restrictIoi]
    split_ifs <;> rfl
  right_inv p := Prod.ext (funext fun e ↦ by simp [restrictIic, Set.mem_Iic.1 e.2])
    (funext fun e ↦ by simp [restrictIoi, not_le.2 (Set.mem_Ioi.1 e.2)])
  measurable_toFun := (measurable_restrictIic d).prodMk (measurable_restrictIoi d)
  measurable_invFun := Measurable.of_eval fun e ↦ by
    change Measurable fun p : (Set.Iic d → β) × (Set.Ioi d → β) ↦
      if h : e ≤ d then p.1 ⟨e, h⟩ else p.2 ⟨e, not_le.1 h⟩
    split_ifs <;> fun_prop

@[simp]
lemma splitIicIoi_apply {T β : Type} [LinearOrder T] [MeasurableSpace β] (d : T) (y : T → β) :
    splitIicIoi d y = (restrictIic d y, restrictIoi d y) :=
  rfl

@[fun_prop]
lemma measurable_splitIicIoi_symm {T β : Type} [LinearOrder T] [MeasurableSpace β] (d : T) :
    Measurable (splitIicIoi (β := β) d).symm :=
  (splitIicIoi d).symm.measurable

/-- Gluing a past and a future: the inverse of `splitIicIoi d`. -/
lemma splitIicIoi_symm_apply {T β : Type} [LinearOrder T] [MeasurableSpace β] (d : T)
    (p : (Set.Iic d → β) × (Set.Ioi d → β)) (e : T) :
    (splitIicIoi d).symm p e = if h : e ≤ d then p.1 ⟨e, h⟩ else p.2 ⟨e, not_le.1 h⟩ :=
  rfl

@[simp]
lemma restrictIic_splitIicIoi_symm {T β : Type} [LinearOrder T] [MeasurableSpace β] (d : T)
    (p : (Set.Iic d → β) × (Set.Ioi d → β)) : restrictIic d ((splitIicIoi d).symm p) = p.1 :=
  congrArg Prod.fst ((splitIicIoi d).apply_symm_apply p)

@[simp]
lemma restrictIoi_splitIicIoi_symm {T β : Type} [LinearOrder T] [MeasurableSpace β] (d : T)
    (p : (Set.Iic d → β) × (Set.Ioi d → β)) : restrictIoi d ((splitIicIoi d).symm p) = p.2 :=
  congrArg Prod.snd ((splitIicIoi d).apply_symm_apply p)

@[simp]
lemma splitIicIoi_symm_restrict {T β : Type} [LinearOrder T] [MeasurableSpace β] (d : T)
    (x : T → β) : (splitIicIoi d).symm (restrictIic d x, restrictIoi d x) = x :=
  (splitIicIoi d).symm_apply_apply x

/-- Follow `x` up to index `d`, and `y` after `d`. -/
def padAfter {T β : Type} [LinearOrder T] (d : T) (x y : T → β) : T → β :=
  fun e ↦ if e ≤ d then x e else y e

@[fun_prop]
lemma measurable_padAfter {T α β : Type} [LinearOrder T] [MeasurableSpace α] [MeasurableSpace β]
    {f g : α → T → β} (d : T) (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x ↦ padAfter d (f x) (g x) :=
  Measurable.of_eval fun e ↦ by
    unfold padAfter
    split_ifs
    · exact (measurable_pi_apply e).comp hf
    · exact (measurable_pi_apply e).comp hg

@[simp]
lemma restrictIic_padAfter {T β : Type} [LinearOrder T] (d : T) (x y : T → β) :
    restrictIic d (padAfter d x y) = restrictIic d x :=
  funext fun e ↦ if_pos (Set.mem_Iic.1 e.2)

@[simp]
lemma restrictIoi_padAfter {T β : Type} [LinearOrder T] (d : T) (x y : T → β) :
    restrictIoi d (padAfter d x y) = restrictIoi d y :=
  funext fun e ↦ if_neg (not_le.2 (Set.mem_Ioi.1 e.2))

/-- Applying `Kernel.id ×ₖ κ` and then a map `f`. -/
lemma ProbabilityTheory.Kernel.map_id_prod_apply {α β γ : Type} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] (κ : Kernel α β) [IsSFiniteKernel κ]
    {f : α × β → γ} (hf : Measurable f) (x : α) :
    (Kernel.id ×ₖ κ).map f x = (κ x).map (fun y ↦ f (x, y)) := by
  rw [Kernel.map_apply _ hf, Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    Measure.map_map hf measurable_prodMk_left]
  rfl

/-- Pushing a composition-product forward along `(x, y) ↦ (f x, g x y)` gives a
composition-product, as soon as the law of `g x` under `R x` only depends on `f x`. -/
lemma MeasureTheory.Measure.map_compProd_eq {α β γ δ : Type} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ] (μ : Measure α) [SFinite μ]
    (R : Kernel α β) [IsSFiniteKernel R] {f : α → γ} (hf : Measurable f) {g : α → β → δ}
    (hg : Measurable fun p : α × β ↦ g p.1 p.2) (η : Kernel γ δ) [IsSFiniteKernel η]
    (h : ∀ x, (R x).map (g x) = η (f x)) :
    (μ ⊗ₘ R).map (fun p ↦ (f p.1, g p.1 p.2)) = μ.map f ⊗ₘ η := by
  ext s hs
  have hF : Measurable fun p : α × β ↦ (f p.1, g p.1 p.2) := (hf.comp measurable_fst).prodMk hg
  rw [Measure.map_apply hF hs, Measure.compProd_apply (hF hs), Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  refine lintegral_congr fun x ↦ ?_
  have hgx : Measurable (g x) := hg.comp measurable_prodMk_left
  rw [← h x, Measure.map_apply hgx (measurable_prodMk_left hs)]
  rfl

/-- A kernel from an initial state and an action path to a path of (state, observation) pairs is
*causal and Markov* if, at every index `d`, its output splits (along `splitIicIoi d`) into
* a past (indices `≤ d`) that only depends on the initial state and the actions at indices `≤ d`,
* followed by a future (indices `> d`) that only depends on the state at index `d` and the actions
  at indices `> d`.

In discrete time this says that each output only depends on the current state and action (see
the paper's Definition 1); the formulation makes equal sense in continuous time. -/
def ProbabilityTheory.Kernel.IsCausalMarkov {T A O S : Type} [LinearOrder T] [MeasurableSpace A]
    [MeasurableSpace O] [MeasurableSpace S] (κ : Kernel (S × (T → A)) (T → S × O)) : Prop :=
  ∀ d : T, ∃ (past : Kernel (S × (Set.Iic d → A)) (Set.Iic d → S × O))
    (future : Kernel (S × (Set.Ioi d → A)) (Set.Ioi d → S × O)),
    IsMarkovKernel past ∧ IsMarkovKernel future ∧ ∀ s a,
      (κ (s, a)).map (splitIicIoi d) =
        past (s, restrictIic d a) ⊗ₘ
          future.comap (fun z ↦ ((z ⟨d, Set.mem_Iic.2 le_rfl⟩).1, restrictIoi d a)) (by fun_prop)
