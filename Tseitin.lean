import Mathlib.Tactic

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

#check Atom

#check ¬ (Atom 2)
#check (Atom 2) → (Atom 3).Neg

def Valuation.eval (v : Valuation) (F : Formula) := match F with
  | Atom n => v n
  | .Neg f => ! v.eval f
  | .Imp f1 f2 => if v.eval f1 == true then v.eval f2 else true

open Valuation

#eval eval (fun x => x % 2 == 0) $ (Atom 1).Imp (Atom 4)

def Satisfies (v) (F) := eval v F = true

notation v " ⊨ " F => Satisfies v F

abbrev Satisfiable (F : Formula) := ∃ v, v ⊨ F

notation F "sat." => Satisfiable F

#check (Atom 2) sat.

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


#check countable_iff_exists_injective

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

lemma BigAnd.append {f g : List Formula} (hf : f ≠ []) (hg : g ≠ []) : (⋀ f ++ g) (by grind) = (⋀ f) hf ∧ (⋀ g) hg := by
  sorry

@[simp] lemma BigAnd.single {f : Formula} (hf) : (⋀ [f]) hf = f := by
  sorry

#check Set.iUnion_accumulate
#check Set.subset_accumulate
#check Set.subset_iUnion

lemma Ns_eq_empty_iff {f : Formula} : (Ns f = []) ↔ ¬ NonAtomic f := by
  simp [NonAtomic]
  split
  · simp [Ns]
  · cases f <;> simp_all [Ns, N]

lemma neg_sub {g f : Formula} (h : (¬g) ∈ Sub f) : g ∈ Sub f := by
  sorry

lemma eval_not {v w : Valuation} {f} (hf : NonAtomic f) (hw : w ⊨ T f hf)
  (h : ∀ n ∈ Atoms f, v n = w.eval (V (Atom n))) : ∀ g ∈ Sub f, w.eval (V (¬g)) = ! w.eval (V g) := by
  intro g hg
  induction g with
  | Atom n =>
    have := h n sorry
    rw [← this]
    sorry
    -- contradiction
  | Neg g ih' =>
    specialize ih' ?_
    exact neg_sub hg
    rw [ih']
    simp
    sorry
  | Imp f1 f2 f1_ih f2_ih => sorry

-- Exercise 3 a
lemma subformula {f} {v w : Valuation} (hf : NonAtomic f) (hw : w ⊨ T f hf)
  (h : ∀ n ∈ Atoms f, v n = w.eval (V (Atom n))) : ∀ g ∈ Sub f, w.eval (V g) = v.eval g := by
  intro g hg
  induction g with
  | Atom n =>
    specialize h n ?_
    · apply mem_atoms_of_subformula hg
    · rw [← h]
      rfl
  | Neg g ih =>

    sorry
  | Imp f1 f2 f1_ih f2_ih => sorry


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
