import Mathlib.Tactic.Have
import Mathlib.Tactic.ApplyAt

import Mathlib.Tactic.DeriveCountable

namespace LHCP

inductive Formula where
  | Atom (n : ℕ)
  | Neg (f : Formula)
  | Imp (f1 f2 : Formula)
deriving Countable

notation "¬" f => Formula.Neg f

notation f1 " → " f2 => Formula.Imp f1 f2

open Formula

abbrev Valuation := ℕ → Bool

-- We can use notation like this
-- #check ¬ (Atom 2)
-- #check (Atom 2) → (Atom 3).Neg

def Valuation.eval (v : Valuation) (F : Formula) := match F with
  | Atom n => v n
  | .Neg f => ! v.eval f
  | .Imp f1 f2 => v.eval f1 → v.eval f2
    -- Equivalent form with if-then-else `if v.eval f1 == true then v.eval f2 else true`

open Valuation

-- #eval eval (fun x => x % 2 == 0) $ (Atom 1).Imp (Atom 4)

abbrev Satisfies (v) (F) := eval v F = true

notation v " ⊨ " F => Satisfies v F

abbrev Satisfiable (F : Formula) := ∃ v, v ⊨ F

notation F "sat." => Satisfiable F

-- #check (Atom 2) sat.

example : ((Atom 1) → ¬ (Atom 4)) sat. := by
  use (fun x => x % 2 == 0)
  rfl

def Formula.And (A B : Formula) : Formula := ¬ (A → ¬ B)

notation f1 " ∧ " f2 => Formula.And f1 f2

def Formula.Iff (A B : Formula) : Formula := (A → B) ∧ (B → A)

notation f1 " ↔ " f2 => Formula.Iff f1 f2

def Formula.BigAnd (l : List Formula) (hl : l ≠ []) : Formula := match l with
-- | [] => nomatch hl (refl []) -- lean can deduce that this is not needed
| [f] => f
| f :: g :: gs => f ∧ BigAnd (g :: gs) (by simp_all)

notation "⋀ " l => BigAnd l

def NonAtomic (f : Formula) := match f with
| Atom _ => False
| _ => True

@[simp] lemma NonAtomic.neg (f : Formula) : NonAtomic $ ¬ f := by
  simp_all [NonAtomic]

@[simp] lemma NonAtomic.imp (f1 f2 : Formula) : NonAtomic $ f1 → f2 := by
  simp_all [NonAtomic]

lemma Formula.existsChooseFn : ∃ F : Formula → ℕ, F.Injective := by
  rw [← countable_iff_exists_injective]
  exact inferInstance

noncomputable section
def Formula.choose : Formula → ℕ := Formula.existsChooseFn.choose

lemma Formula.choose_injective : Formula.choose.Injective := by
  exact Formula.existsChooseFn.choose_spec

namespace Tseitin

-- Unique atom for each subformula
def V (f : Formula) := Atom (f.choose)

def N (f : Formula) : List Formula := match f with
| Atom _n => []
| .Neg g => [V f ↔ ¬ V g]
| .Imp g h => [V f ↔ (V g → V h)]

def Ns (f : Formula) : List Formula := match f with
| Atom _ => []
| .Neg g => N f ++ Ns g
| .Imp f1 f2 => N f ++ Ns f1 ++ Ns f2

def T (f : Formula) (hf : NonAtomic f) : Formula := Formula.BigAnd (Ns f) (by
  cases f with
  | Atom n =>
    contradiction -- hf is literally False
  | Neg f =>
    simp [Ns, N]
  | Imp f1 f2 =>
    simp [Ns, N]
)

def E (f : Formula) := match h : f with
| Atom _n => V f
| .Neg g => T f (by simp_all) ∧ V f
| .Imp f1 f2 => T f (by simp_all) ∧ V f

def Atoms (f : Formula) : Set ℕ := match f with
| Atom n => {n}
| .Neg g => Atoms g
| .Imp g h => Atoms g ∪ Atoms h


def Sub (f : Formula) : Set Formula := match f with
| Atom n => {Atom n}
| .Neg g => {.Neg g} ∪ Sub g
| .Imp g h => {.Imp g h} ∪ Sub g ∪ Sub h

lemma mem_atoms_of_subformula {m g} (h : Atom m ∈ Sub g) : m ∈ Atoms g := by
  induction g with
  | Atom n =>
    simp [Sub] at h
    simp [Atoms]
    exact h
  | Neg f ih =>
    simp [Sub] at h
    specialize ih h
    simp [Atoms]
    exact ih
  | Imp f1 f2 f1_ih f2_ih =>
    simp [Sub] at h
    cases h with
    | inl h =>
      specialize f1_ih h
      simp [Atoms]
      left
      exact f1_ih
    | inr h =>
      specialize f2_ih h
      simp [Atoms]
      right
      exact f2_ih

@[simp] lemma BigAnd.cons {f} {fs : List Formula} (hf : fs ≠ []) :
  (⋀ f :: fs) (List.cons_ne_nil f fs) = f ∧ (⋀ fs) hf := by
  cases fs with
  | nil => contradiction
  | cons head tail =>
    rfl

@[simp] lemma BigAnd.single {f : Formula} (hf) : (⋀ [f]) hf = f := rfl

@[simp] lemma Satisfies.and {w f g} : (w ⊨ f ∧ g) ↔ (w ⊨ f) ∧ w ⊨ g := by
  simp [Satisfies, Formula.And, eval]

@[simp] lemma Satisfies.iff {w f g} : (w ⊨ f ↔ g) ↔ ((w ⊨ f) ↔ w ⊨ g) := by
  simp [Satisfies, Formula.Iff, eval]
  grind

@[simp] lemma Satisfies.bigAnd {w : Valuation} {l : List Formula} (hl : l ≠ []) : (w ⊨ (⋀ l) hl) ↔ ∀ g ∈ l, w ⊨ g := by
  induction l with
  | nil => contradiction
  | cons head tail ih =>
    by_cases htail : tail = []
    · subst tail
      simp
    · specialize ih htail
      rw [BigAnd.cons htail]
      rw [Satisfies.and]
      rw [ih]
      simp

@[simp] lemma Satisfies.bigAnd_append {w} {f g : List Formula} (hf : f ≠ []) (hg : g ≠ []) : (w ⊨ (⋀ f ++ g) (List.append_ne_nil_of_left_ne_nil hf g)) ↔ w ⊨ (⋀ f) hf ∧ (⋀ g) hg := by
  induction f with
  | nil => contradiction
  | cons head tail ih =>
    by_cases htail : tail = []
    · subst htail
      simp [hg]
    · have : tail ++ g ≠ []
      · grind
      simp [BigAnd.cons, this, htail]
      grind

@[grind] lemma Ns_eq_empty_iff {f : Formula} : (Ns f = []) ↔ ¬ NonAtomic f := by
  simp [NonAtomic]
  split
  · simp [Ns]
  · cases f <;> simp_all [Ns, N]

lemma N_sub_subset_Ns {f s : Formula} (hs : s ∈ Sub f) : N s ⊆ Ns f := by
  induction f with
  | Atom n =>
    simp [Sub] at hs
    subst hs
    simp [N, Ns]
  | Neg f ih =>
    simp only [Sub, Ns] at hs ⊢
    cases hs with
    | inl h =>
      subst h
      simp [N]
    | inr hsub =>
      intros cl hc
      apply List.mem_append_right
      exact ih hsub hc
  | Imp f1 f2 ih1 ih2 =>
    simp only [Sub, Ns] at hs ⊢
    cases hs with
    | inl h =>
      simp at h
      cases h <;> simp_all
    | inr h =>
      simp_all

@[grind] lemma not_nonAtomic {f} : (¬ NonAtomic f) ↔ ∃ n, f = Atom n := by
  simp_all [NonAtomic]
  split <;> grind

@[simp, grind] lemma sub_self {f : Formula} : f ∈ Sub f := by
  cases f <;> simp [Sub]

@[grind] lemma sub_neg {g f : Formula} (h : g ∈ Sub f) : g ∈ Sub (¬ f) := by
  simp_all [Sub]

@[grind] lemma sub_imp {g f1 f2 : Formula} (h : g ∈ Sub f1 ∨ g ∈ Sub f2) : g ∈ Sub (f1 → f2) := by
  cases h <;> simp_all [Sub]

@[grind] lemma neg_sub {g f : Formula} (h : (¬g) ∈ Sub f) : g ∈ Sub f := by
  induction f generalizing g with
  | Atom n => simp [Sub] at h
  | Neg f ih =>
    simp [Sub] at *
    grind
  | Imp f1 f2 ih1 ih2 =>
    simp [Sub] at *
    grind

@[grind] lemma imp_sub {g1 g2 f : Formula} (h : (g1 → g2) ∈ Sub f) : (g1 ∈ Sub f) ∧ g2 ∈ Sub f := by
  induction f generalizing g1 g2 with
  | Atom n => simp [Sub] at h
  | Neg f ih =>
    simp [Sub] at *
    grind
  | Imp f1 f2 ih1 ih2 =>
    simp [Sub] at *
    rcases h with (⟨rfl, rfl⟩ | h) | h
    · simp
    · grind
    · grind

-- Turns out the subformula definition should have been strict
-- We don't want this to be abbrev, otherwise simp reduces Ssub to Sub in assumptions
def Ssub (f : Formula) : Set Formula := Sub f \ {f}

lemma mem_ssub (f g) : (g ∈ Ssub f) ↔ (g ≠ f) ∧ g ∈ Sub f := by
  unfold Ssub
  grind

lemma sub_smaller {g f : Formula} (h : g ∈ Sub f) : sizeOf g ≤ sizeOf f := by
  induction f generalizing g with
  | Atom n =>
    simp_all [Sub]
  | Neg f ih =>
    simp [Sub] at h
    cases h with
    | inl h => grind
    | inr h =>
      specialize ih h
      simp
      omega
  | Imp f1 f2 f1_ih f2_ih =>
    simp [Sub] at h
    rcases h with ((h | h) | h)
    · grind
    · specialize f1_ih h
      simp
      omega
    · specialize f2_ih h
      simp
      omega

lemma neg_ssub {g f : Formula} (h : (¬g) ∈ Ssub f) : g ∈ Ssub f := by
  induction f generalizing g with
  | Atom n =>
    simp_all [Ssub, Sub]
  | Neg f ih =>
    simp_all [Ssub, Sub]
    grind -- uses neg_sub
  | Imp f1 f2 f1_ih f2_ih =>
    have hf12 : g ≠ f1 → f2
    · intro contra
      subst g
      simp [Ssub, Sub] at h
      rcases h with h | h
      · apply sub_smaller at h
        contrapose h
        simp
        omega
      · apply sub_smaller at h
        contrapose h
        simp
        omega

    obtain ⟨h1, h2⟩ := h
    simp only [Set.mem_singleton_iff] at h2
    refine ⟨?_, hf12⟩
    simp [Sub] at h1
    cases h1 with
    | inl h =>
      apply neg_sub at h
      simp [Sub, h]
    | inr h =>
      apply neg_sub at h
      simp [Sub, h]

lemma imp_ssub {g1 g2 f : Formula} (h : (g1 → g2) ∈ Ssub f) : (g1 ∈ Ssub f) ∧ g2 ∈ Ssub f := by
  induction f generalizing g1 g2 with
  | Atom n =>
    simp_all [Ssub, Sub]
  | Neg f ih =>
    simp_all [Ssub, Sub]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · grind
    · rintro rfl
      apply sub_smaller at h
      contrapose h
      simp
      omega
    · grind
    · rintro rfl
      apply sub_smaller at h
      contrapose h
      simp
      omega
  | Imp f1 f2 f1_ih f2_ih =>
    simp [Ssub] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · have := imp_sub h1
      grind
    · rintro rfl
      apply sub_smaller at h1
      contrapose h1
      simp
      omega
    · have := imp_sub h1
      grind
    · rintro rfl
      apply sub_smaller at h1
      contrapose h1
      simp
      omega

lemma eval_not {w f} (hf : NonAtomic f) (hw : w ⊨ T f hf) : ∀ g, (g.Neg ∈ Sub f) → w.eval (V (¬g)) = ! w.eval (V g) := by
  intro g hg

  have hclause : (V (¬ g) ↔ ¬ V (g)) ∈ N (¬ g) := by
    simp [N]

  have hclause_in_Ns := N_sub_subset_Ns hg hclause

  simp [T] at hw
  specialize hw _ hclause_in_Ns
  simp [Satisfies.iff] at hw
  simp [hw, eval]

lemma eval_imp {w f} (hf : NonAtomic f) (hw : w ⊨ T f hf) : ∀ g1 g2 : Formula,
    ((g1 → g2) ∈ Sub f) → w.eval (V (g1 → g2)) = (!w.eval (V g1) || w.eval (V g2)) := by
  intro g1 g2 hg

  have hclause : (V (g1 → g2) ↔ (V g1 → V g2)) ∈ N (g1 → g2) := by
    simp [N]

  have hclause_in_Ns := N_sub_subset_Ns hg hclause

  simp [T] at hw
  specialize hw _ hclause_in_Ns
  simp [Satisfies.iff] at hw
  simp [hw, eval]

-- Exercise 3 a
theorem eval_eq_of_mem_ssub {f} {v w : Valuation} (hf : NonAtomic f) (hw : w ⊨ T f hf)
  (h : ∀ n ∈ Atoms f, v n = w.eval (V (Atom n))) : ∀ g ∈ Ssub f, w.eval (V g) = v.eval g := by
  intro g hg
  induction g with
  | Atom n =>
    specialize h n ?_
    · apply mem_atoms_of_subformula hg.1
    · rw [← h]
      rfl
  | Neg g ih =>
    rw [eval_not hf hw g hg.1]
    specialize ih (neg_ssub hg)
    simp [ih, eval]
  | Imp f1 f2 f1_ih f2_ih =>
    rw [eval_imp hf hw f1 f2 hg.1]
    specialize f1_ih (imp_ssub hg).1
    specialize f2_ih (imp_ssub hg).2
    simp [f1_ih, f2_ih, eval]

-- "Tseitin's theorem"
theorem sat_iff {f} (hf : NonAtomic f) : f sat. ↔ E f sat. := by
  constructor
  · -- (→)
    intro h
    obtain ⟨v, hv⟩ := h
    sorry

  · -- (←)
    intro h
    obtain ⟨w, hw⟩ := h

    sorry
