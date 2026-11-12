-- The trusted specification: syntax, semantics, derivations, and Theorem 1. Lean core only.
namespace Stackat

/-- Expressions over a stack alphabet `A`. -/
inductive Expr (A : Type) where
  | zero | one | push (a : A) | pop (a : A)
  | add (e f : Expr A) | mul (e f : Expr A) | star (e : Expr A)

-- Notation: 0, 1, e + f, e * f and e⋆ stand for zero, one, add, mul and star.
instance : Zero (Expr A) := ⟨.zero⟩
instance : One (Expr A) := ⟨.one⟩
instance : Add (Expr A) := ⟨.add⟩
instance : Mul (Expr A) := ⟨.mul⟩
scoped postfix:max "⋆" => Stackat.Expr.star

/-- `Steps r s t`: `t` is reached from `s` by zero or more `r`-steps. -/
inductive Steps (r : α → α → Prop) : α → α → Prop
  | refl : Steps r s s
  | step : r s m → Steps r m t → Steps r s t

/-- The relation `R e` between input and output stacks, written top first. -/
def R : Expr A → List A → List A → Prop
  | 0 => fun _ _ => False
  | 1 => Eq
  | .push a => fun s t => t = a :: s
  | .pop a => fun s t => s = a :: t
  | e + f => fun s t => R e s t ∨ R f s t
  | e * f => fun s t => ∃ m, R e s m ∧ R f m t        -- `e` runs first
  | e⋆ => Steps (R e)

set_option hygiene false
scoped notation:25 "⊢ " e:51 " ≈ " f:51 => Stackat.Derives e f        -- `e = f` is derivable
scoped notation:25 "⊢ " e:51 " ≤ " f:51 => Stackat.Derives (e + f) f  -- `e ≤ f` is `e + f = f`

/-- Derivability from the Kleene algebra laws and exactly the three stack laws. -/
inductive Derives {A : Type} : Expr A → Expr A → Prop where
  | refl : ⊢ e ≈ e                                         -- equational reasoning
  | symm : ⊢ e ≈ f → ⊢ f ≈ e
  | trans : ⊢ e ≈ f → ⊢ f ≈ g → ⊢ e ≈ g
  | add_congr : ⊢ e ≈ e' → ⊢ f ≈ f' → ⊢ e + f ≈ e' + f'
  | mul_congr : ⊢ e ≈ e' → ⊢ f ≈ f' → ⊢ e * f ≈ e' * f'
  | star_congr : ⊢ e ≈ f → ⊢ e⋆ ≈ f⋆
  | add_assoc : ⊢ (e + f) + g ≈ e + (f + g)                -- idempotent semiring
  | add_comm : ⊢ e + f ≈ f + e
  | add_zero : ⊢ e + 0 ≈ e
  | add_idem : ⊢ e + e ≈ e
  | mul_assoc : ⊢ (e * f) * g ≈ e * (f * g)
  | one_mul : ⊢ 1 * e ≈ e
  | mul_one : ⊢ e * 1 ≈ e
  | zero_mul : ⊢ 0 * e ≈ 0
  | mul_zero : ⊢ e * 0 ≈ 0
  | mul_add : ⊢ e * (f + g) ≈ e * f + e * g
  | add_mul : ⊢ (e + f) * g ≈ e * g + f * g
  | star_unfold_left : ⊢ 1 + e * e⋆ ≈ e⋆                   -- Kleene star
  | star_unfold_right : ⊢ 1 + e⋆ * e ≈ e⋆
  | star_induct_left : ⊢ e * f ≤ f → ⊢ e⋆ * f ≤ f
  | star_induct_right : ⊢ f * e ≤ f → ⊢ f * e⋆ ≤ f
  | push_pop : ⊢ .push a * .pop a ≈ 1                      -- the three stack laws
  | push_pop_ne : a ≠ b → ⊢ .push a * .pop b ≈ 0
  | pop_push : ⊢ .pop a * .push a ≤ 1

/-- **Theorem 1**, for every alphabet: `R e ⊆ R f` iff `⊢ e ≤ f`. -/
def SoundnessAndCompleteness : Prop :=
  ∀ (A : Type) (e f : Expr A), (∀ s t, R e s t → R f s t) ↔ ⊢ e ≤ f

end Stackat
