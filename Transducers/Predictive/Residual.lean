import Transducers.Predictive.FutureFrom

/-!
# Residual interfaces and predictive equivalence

A *finite history* `h` is a number `k` of steps, with the actions and observations at times
`0, …, k - 1`. The *residual* of an interface `I` at `h` (the paper's `I_h`, Eq. (4)) is the law of
the observations after `h`, given the actions after `h`, re-indexed to start at time `0`. It is read
off `I.futureFrom k`, so it is defined for every history, and depends on no choice of conditional
law.

Two histories are *predictively equivalent* if they have the same residual. Extending equivalent
histories by the same steps keeps them equivalent, as long as the extension has positive
probability (`Interface.resid_append_eq`); this needs the observations to have measurable
singletons. Extensions of probability zero are dropped: `Interface.upd` extends a class of
histories by a step only if the step has positive probability.

## Main results

* `Interface.resid`: the residual of an interface at a finite history.
* `Interface.histSetoid`: predictive equivalence of histories.
* `Interface.resid_append_eq`: predictive equivalence is preserved by extensions of positive
  probability.
* `Interface.upd`, `Interface.run`: updating a class of histories by one step, and along a path.
* `Interface.ae_run_eq`: for countable observations, almost surely the run from the class of `h` is
  the class of `h` extended by the history so far.
-/

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel

open scoped ENNReal

noncomputable section

variable {A O : Type} [MeasurableSpace A] [MeasurableSpace O]

/-! ### Finite histories -/

/-- A finite history: a number `k` of steps, with the actions and observations at times
`0, …, k - 1`. -/
abbrev FinHist (A O : Type) := Σ k : ℕ, (Fin k → A) × (Fin k → O)

namespace FinHist

/-- The empty history. -/
def empty : FinHist A O := ⟨0, Fin.elim0, Fin.elim0⟩

/-- The history `h` followed by the history `u`. -/
def append (h u : FinHist A O) : FinHist A O :=
  ⟨h.1 + u.1, Fin.append h.2.1 u.2.1, Fin.append h.2.2 u.2.2⟩

/-- A single step: the action `x` and the observation `y`. -/
def single (x : A) (y : O) : FinHist A O := ⟨1, fun _ ↦ x, fun _ ↦ y⟩

/-- The history of the first `n` steps of the actions `a` and the observations `o`. -/
def pref (n : ℕ) (a : ℕ → A) (o : ℕ → O) : FinHist A O := ⟨n, restrictFin n a, restrictFin n o⟩

omit [MeasurableSpace A] [MeasurableSpace O] in
lemma append_pref_zero (h : FinHist A O) (a : ℕ → A) (o : ℕ → O) : h.append (pref 0 a o) = h := by
  refine Sigma.ext rfl (heq_of_eq (Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_)))
  all_goals
    simp only [append, pref]
    exact fin_append_apply_of_lt _ _ i i.isLt

omit [MeasurableSpace A] [MeasurableSpace O] in
lemma _root_.restrictFin_succ {β : Type} (x : ℕ → β) (n : ℕ) :
    restrictFin (n + 1) x = Fin.snoc (restrictFin n x) (x n) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [restrictFin]
  | cast i => simp [restrictFin]

omit [MeasurableSpace A] [MeasurableSpace O] in
lemma _root_.fin_append_restrictFin_succ {β : Type} {k : ℕ} (b : Fin k → β) (x : ℕ → β) (n : ℕ) :
    Fin.append b (restrictFin (n + 1) x) =
      (Fin.append (m := k + n) (n := 1) (Fin.append b (restrictFin n x)) (fun _ ↦ x n) :
        Fin (k + (n + 1)) → β) := by
  rw [restrictFin_succ, Fin.append_snoc, Fin.append_right_eq_snoc]

omit [MeasurableSpace A] [MeasurableSpace O] in
lemma append_pref_succ (h : FinHist A O) (a : ℕ → A) (o : ℕ → O) (n : ℕ) :
    h.append (pref (n + 1) a o) = (h.append (pref n a o)).append (single (a n) (o n)) :=
  Sigma.ext rfl (heq_of_eq (Prod.ext (fin_append_restrictFin_succ _ _ _)
    (fin_append_restrictFin_succ _ _ _)))

end FinHist

/-- Follow the entries of `b` up to time `k`, then the entries of `c`. -/
def glue {β : Type} {k : ℕ} (b : Fin k → β) (c : ℕ → β) : ℕ → β :=
  fun i ↦ if h : i < k then b ⟨i, h⟩ else c (i - k)

@[fun_prop]
lemma measurable_glue {β : Type} [MeasurableSpace β] {k : ℕ} (b : Fin k → β) :
    Measurable (glue b) :=
  Measurable.of_eval fun i ↦ by
    unfold glue
    split_ifs
    · exact measurable_const
    · exact measurable_pi_apply _

lemma glue_append {β : Type} {k j : ℕ} (b : Fin k → β) (b' : Fin j → β) (c : ℕ → β) :
    glue (Fin.append b b') c = glue b (glue b' c) := by
  funext i
  simp only [glue]
  split_ifs
  all_goals first
    | omega
    | (rw [fin_append_apply_of_lt _ _ _ (by simp; omega)])
    | (rw [fin_append_apply_of_le _ _ _ (by simp; omega)])
    | (congr 1; omega)

lemma restrictFin_glue {β : Type} {k : ℕ} (b : Fin k → β) (c : ℕ → β) :
    restrictFin k (glue b c) = b :=
  funext fun i ↦ by simp [restrictFin, glue]

lemma restrictFin_glue_glue {β : Type} {k j : ℕ} (b : Fin k → β) (b' : Fin j → β) (c : ℕ → β) :
    restrictFin (k + j) (glue b (glue b' c)) = Fin.append b b' := by
  rw [← glue_append, restrictFin_glue]

lemma glue_restrictFin_shiftBy {β : Type} (j : ℕ) (o : ℕ → β) :
    glue (restrictFin j o) (shiftBy j o) = o := by
  funext i
  simp only [glue, restrictFin, shiftBy]
  split_ifs
  · rfl
  · congr 1
    omega

lemma glue_elim0 {β : Type} (c : ℕ → β) : glue (Fin.elim0 : Fin 0 → β) c = c :=
  funext fun i ↦ by simp [glue]

namespace Interface

variable (I : Interface A O)

/-! ### Residuals -/

/-- **The residual of `I` at the history `h`** (the paper's `I_h`): the law of the observations
after `h`, given the actions after `h`, re-indexed to start at time `0`. -/
def resid (h : FinHist A O) : Kernel (ℕ → A) (ℕ → O) :=
  (I.futureFrom h.1).comap (fun c ↦ (glue h.2.1 c, h.2.2)) (by fun_prop)

instance (h : FinHist A O) : IsMarkovKernel (I.resid h) :=
  IsMarkovKernel.comap _ _

lemma resid_apply (h : FinHist A O) (c : ℕ → A) :
    I.resid h c = I.futureFrom h.1 (glue h.2.1 c, h.2.2) :=
  rfl

/-- The residual at the empty history is the observation kernel. -/
lemma resid_empty : I.resid FinHist.empty = I.obsKernel := by
  ext1 c
  rw [resid_apply, FinHist.empty, glue_elim0, futureFrom_zero]

/-- The probability of the steps `u` after the history `h`. -/
def extProb (h u : FinHist A O) : ℝ≥0∞ :=
  I.horizon h.1 u.1 (Fin.append h.2.1 u.2.1) h.2.2 {u.2.2}

/-- After `h`, the next `u.1` observations, given the actions `u.2.1` and then any actions, have
law `horizon`. -/
lemma resid_map_restrictFin (h : FinHist A O) (j : ℕ) (b : Fin j → A) (c : ℕ → A) :
    (I.resid h (glue b c)).map (restrictFin j) = I.horizon h.1 j (Fin.append h.2.1 b) h.2.2 := by
  rw [resid_apply, futureFrom_map_restrictFin, restrictFin_glue_glue]

/-- After `h`, on the actions `a`, the next `j` observations have law `horizon`. -/
lemma resid_map_restrictFin' (h : FinHist A O) (j : ℕ) (a : ℕ → A) :
    (I.resid h a).map (restrictFin j) =
      I.horizon h.1 j (Fin.append h.2.1 (restrictFin j a)) h.2.2 := by
  conv_lhs => rw [← glue_restrictFin_shiftBy j a]
  exact I.resid_map_restrictFin h j (restrictFin j a) (shiftBy j a)

/-- **Splitting a residual.** After the history `h`, the next `j` observations are drawn from
`horizon`, and the later observations from the residual at the extended history. -/
lemma resid_map_split (h : FinHist A O) (j : ℕ) (b : Fin j → A) (c : ℕ → A) :
    (I.resid h (glue b c)).map (fun y ↦ (restrictFin j y, shiftBy j y)) =
      I.horizon h.1 j (Fin.append h.2.1 b) h.2.2 ⊗ₘ
        (I.futureFrom (h.1 + j)).comap (fun v ↦ (glue (Fin.append h.2.1 b) c, Fin.append h.2.2 v))
          (measurable_const.prodMk (measurable_fin_append_right _)) := by
  rw [resid_apply, futureFrom_map_split, restrictFin_glue_glue, glue_append]

/-! ### Predictive equivalence -/

/-- **Predictive equivalence**: two histories are equivalent if they have the same residual. -/
def histSetoid : Setoid (FinHist A O) where
  r h h' := I.resid h = I.resid h'
  iseqv := ⟨fun _ ↦ rfl, Eq.symm, Eq.trans⟩

/-- Equivalent histories give the same probability to every extension. -/
lemma extProb_eq_of_resid_eq {h h' : FinHist A O} (hh : I.resid h = I.resid h') (u : FinHist A O) :
    I.extProb h u = I.extProb h' u := by
  obtain ⟨_ | m, b, w⟩ := u
  · rfl
  · have := congrArg (fun κ : Kernel (ℕ → A) (ℕ → O) ↦
      (κ (glue b fun _ ↦ b 0)).map (restrictFin (m + 1)) {w}) hh
    simp only [resid_map_restrictFin] at this
    exact this

variable [MeasurableSingletonClass O]

/-- **Extending equivalent histories.** If `h` and `h'` have the same residual, and the steps `u`
have positive probability after `h`, then `h` and `h'` extended by `u` have the same residual. -/
theorem resid_append_eq {h h' : FinHist A O} (hh : I.resid h = I.resid h') (u : FinHist A O)
    (hu : I.extProb h u ≠ 0) : I.resid (h.append u) = I.resid (h'.append u) := by
  obtain ⟨j, b, w⟩ := u
  ext c B hB
  have hsplit := I.resid_map_split h j b c
  rw [hh, resid_map_split] at hsplit
  have hfst : I.horizon h'.1 j (Fin.append h'.2.1 b) h'.2.2 =
      I.horizon h.1 j (Fin.append h.2.1 b) h.2.2 := by
    rw [← resid_map_restrictFin (c := c), ← resid_map_restrictFin (c := c), hh]
  have key := congrArg (fun μ : Measure ((Fin j → O) × (ℕ → O)) ↦ μ ({w} ×ˢ B)) hsplit
  simp only [Measure.compProd_apply_prod (measurableSet_singleton w) hB, lintegral_singleton,
    comap_apply, hfst] at key
  have hne : I.horizon h.1 j (Fin.append h.2.1 b) h.2.2 {w} ≠ 0 := hu
  have hfin : I.horizon h.1 j (Fin.append h.2.1 b) h.2.2 {w} ≠ ∞ := measure_ne_top _ _
  rw [glue_append, glue_append] at key
  simp only [resid_apply, FinHist.append, glue_append]
  exact ((ENNReal.mul_left_inj hne hfin).1 key).symm

/-- The residual of a class of histories. -/
def residQ (c : Quotient I.histSetoid) : Kernel (ℕ → A) (ℕ → O) :=
  Quotient.lift I.resid (fun _ _ h ↦ h) c

instance (c : Quotient I.histSetoid) : IsMarkovKernel (I.residQ c) := by
  induction c using Quotient.inductionOn
  exact inferInstanceAs (IsMarkovKernel (I.resid _))

omit [MeasurableSingletonClass O] in
lemma residQ_mk (h : FinHist A O) : I.residQ ⟦h⟧ = I.resid h :=
  rfl

open Classical in
/-- **Updating a class of histories** by the steps `u`: extend it by `u` if `u` has positive
probability, and keep it otherwise. -/
def upd (c : Quotient I.histSetoid) (u : FinHist A O) : Quotient I.histSetoid :=
  Quotient.lift (fun h ↦ if I.extProb h u ≠ 0 then ⟦h.append u⟧ else ⟦h⟧)
    (fun h h' (hh : I.resid h = I.resid h') ↦ by
      simp only [I.extProb_eq_of_resid_eq hh u]
      split_ifs with hu
      · exact Quotient.sound (I.resid_append_eq hh u (by rwa [I.extProb_eq_of_resid_eq hh u]))
      · exact Quotient.sound hh) c

open Classical in
lemma upd_mk (h u : FinHist A O) :
    I.upd ⟦h⟧ u = if I.extProb h u ≠ 0 then ⟦h.append u⟧ else ⟦h⟧ :=
  rfl

/-- The run of classes of histories from `c`, along the actions `a` and the observations `o`: at
time `n`, the class after the first `n` steps. -/
def run (c : Quotient I.histSetoid) (a : ℕ → A) (o : ℕ → O) : ℕ → Quotient I.histSetoid
  | 0 => c
  | n + 1 => I.upd (run c a o n) (FinHist.single (a n) (o n))

/-- Almost surely, every step of the observations has positive probability given the history
before it. -/
lemma ae_extProb_ne_zero [Countable O] (h : FinHist A O) (a : ℕ → A) (n : ℕ) :
    ∀ᵐ o ∂I.resid h a,
      I.extProb (h.append (FinHist.pref n a o)) (FinHist.single (a n) (o n)) ≠ 0 := by
  -- The law of the next observation after the first `n`.
  let H : (Fin n → O) → Measure (Fin 1 → O) := fun v ↦
    I.horizon (h.1 + n) 1 (restrictFin (h.1 + n + 1) (glue h.2.1 a)) (Fin.append h.2.2 v)
  have hH : ∀ v, ∀ᵐ x ∂H v, H v {x} ≠ 0 := fun v ↦ by
    rw [ae_iff]
    simp only [ne_eq, not_not]
    have : {x | H v {x} = 0} = ⋃ x ∈ {x | H v {x} = 0}, {x} := (Set.biUnion_of_singleton _).symm
    rw [this, measure_biUnion_null_iff (Set.to_countable _)]
    exact fun x hx ↦ hx
  -- Rewrite the step probability through the split of `o` after `n` observations.
  have hext : ∀ o : ℕ → O,
      I.extProb (h.append (FinHist.pref n a o)) (FinHist.single (a n) (o n)) =
        H (restrictFin n o) {restrictFin 1 (shiftBy n o)} := by
    intro o
    simp only [extProb, H, FinHist.append, FinHist.pref, FinHist.single]
    congr 2
    · funext i
      by_cases hk : (i : ℕ) < h.1 + n
      · rw [fin_append_apply_of_lt _ _ _ hk]
        by_cases hk' : (i : ℕ) < h.1
        · rw [fin_append_apply_of_lt _ _ _ hk']
          simp [restrictFin, glue, hk']
        · rw [fin_append_apply_of_le _ _ _ (not_lt.1 hk')]
          simp [restrictFin, glue, hk']
      · rw [fin_append_apply_of_le _ _ _ (not_lt.1 hk)]
        have := i.isLt
        simp only [restrictFin, glue, show ¬ (i : ℕ) < h.1 by omega, ↓reduceDIte]
        congr 1
        omega
    · funext i
      simp only [restrictFin, shiftBy, Fin.val_eq_zero i, Nat.add_zero]
  have hmeas : MeasurableSet {p : (Fin n → O) × (ℕ → O) | H p.1 {restrictFin 1 p.2} ≠ 0} :=
    (measurableSet_singleton 0).compl.preimage <|
      measurable_from_prod_countable_right fun v ↦ (measurable_of_countable
        fun x : Fin 1 → O ↦ H v {x}).comp (measurable_restrictFin 1)
  have hsplit := I.resid_map_split h n (restrictFin n a) (shiftBy n a)
  rw [glue_restrictFin_shiftBy] at hsplit
  have hae : ∀ᵐ p ∂(I.resid h a).map (fun y ↦ (restrictFin n y, shiftBy n y)),
      H p.1 {restrictFin 1 p.2} ≠ 0 := by
    rw [hsplit]
    refine Measure.ae_compProd_of_ae_ae hmeas (ae_of_all _ fun v ↦ ?_)
    rw [comap_apply]
    change ∀ᵐ r ∂_, H v {restrictFin 1 r} ≠ 0
    refine ae_of_ae_map (p := fun x ↦ H v {x} ≠ 0)
      (measurable_restrictFin (β := O) 1).aemeasurable ?_
    rw [futureFrom_map_restrictFin, glue_append, glue_restrictFin_shiftBy]
    exact hH v
  filter_upwards [ae_of_ae_map ((measurable_restrictFin n).prodMk
    (measurable_shiftBy n)).aemeasurable hae] with o ho
  rwa [hext]

/-- **The run follows the history.** For countable observations, almost surely, at every time `n`
the run from the class of `h` is the class of `h` extended by the first `n` steps. -/
theorem ae_run_eq [Countable O] (h : FinHist A O) (a : ℕ → A) :
    ∀ᵐ o ∂I.resid h a, ∀ n, I.run ⟦h⟧ a o n = ⟦h.append (FinHist.pref n a o)⟧ := by
  filter_upwards [ae_all_iff.2 (I.ae_extProb_ne_zero h a)] with o ho n
  induction n with
  | zero => rw [FinHist.append_pref_zero]; rfl
  | succ n ih =>
    rw [run, ih, upd_mk, ite_eq_left_of_eq_true _ _ (eq_true (ho n)), FinHist.append_pref_succ]

end Interface
