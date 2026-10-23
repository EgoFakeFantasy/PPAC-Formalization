import PPAC.Migration.PureSyntaxQuotation

/-! 纯语法quotation与固定原树变换严格交换，包括任意嵌套量词。仍是编码接口中间层，不替代内部ZF推导。 -/
namespace PPAC.Migration.PureSyntaxOperations
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open PureSyntaxQuotation
open FirstOrder.FormalSystem.ProofT
attribute [local implicit_reducible] SetTheory.signature

theorem term_substitute {sb sf tb tf : Ctx} (b f : Nat → Original.Tree)
    (bs : VariableSubstitution ℒ sb tb tf) (fs : VariableSubstitution ℒ sf tb tf)
    (hb : ∀ {sort} (entry : Variable sb sort), b entry.index = termTree (bs entry))
    (hf : ∀ {sort} (entry : Variable sf sort), f entry.index = termTree (fs entry))
    {sort : SetSort} (input : Tm sb sf sort) :
    SyntaxSubstitution.term b f (termTree input) = termTree (input.substituteMapped bs fs) := by
  exact match input with
  | .bvar entry => hb entry
  | .fvar entry => hf entry
  | .app symbol _ => nomatch symbol

theorem arguments_substitute {sb sf tb tf sorts : Ctx} (b f : Nat → Original.Tree)
    (bs : VariableSubstitution ℒ sb tb tf) (fs : VariableSubstitution ℒ sf tb tf)
    (hb : ∀ {sort} (entry : Variable sb sort), b entry.index = termTree (bs entry))
    (hf : ∀ {sort} (entry : Variable sf sort), f entry.index = termTree (fs entry))
    (input : FirstOrder.Arguments ℒ sb sf sorts) :
    SyntaxSubstitution.terms b f (argumentTrees input) = argumentTrees (input.substituteMapped bs fs) := by
  cases input with
  | nil => rfl
  | cons head tail =>
    simp only [argumentTrees, SyntaxSubstitution.terms, Arguments.substituteMapped,
      term_substitute b f bs fs hb hf head, arguments_substitute b f bs fs hb hf tail]
termination_by sizeOf input

theorem shift_encoding {bound free : Ctx} {sort : SetSort} (input : Tm bound free sort) :
    SyntaxSubstitution.shift (termTree input) = termTree (input.weakenBound SetSort.set) := by
  exact match input with
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .app symbol _ => nomatch symbol

theorem formula_substitute {sb sf tb tf : Ctx} (b f : Nat → Original.Tree)
    (bs : VariableSubstitution ℒ sb tb tf) (fs : VariableSubstitution ℒ sf tb tf)
    (hb : ∀ {sort} (entry : Variable sb sort), b entry.index = termTree (bs entry))
    (hf : ∀ {sort} (entry : Variable sf sort), f entry.index = termTree (fs entry))
    (input : Fm sb sf) :
    SyntaxSubstitution.formula b f (formulaTree input) = formulaTree (input.substituteMapped bs fs) := by
  induction input generalizing tb tf b f with
  | falsum | truth => simp only [formulaTree, NatPacket.leaf, SyntaxSubstitution.formula, Formula.substituteMapped]
  | rel symbol args =>
    cases symbol
    simp only [formulaTree, SyntaxSubstitution.formula, Formula.substituteMapped]
    rw [arguments_substitute b f bs fs hb hf args]
  | equal left right =>
    simp only [formulaTree, SyntaxSubstitution.formula, Formula.substituteMapped]
    rw [term_substitute b f bs fs hb hf left, term_substitute b f bs fs hb hf right]
  | neg body ih => simp only [formulaTree, SyntaxSubstitution.formula, Formula.substituteMapped, ih b f bs fs hb hf]
  | conj left right ihl ihr | disj left right ihl ihr | imp left right ihl ihr | iff left right ihl ihr =>
    simp only [formulaTree, SyntaxSubstitution.formula, Formula.substituteMapped, ihl b f bs fs hb hf, ihr b f bs fs hb hf]
  | forallE sort body ih | existsE sort body ih =>
    cases sort
    simp only [formulaTree, SyntaxSubstitution.formula, Formula.substituteMapped]
    congr 2
    apply ih
    · intro sort entry
      cases entry with
      | here => rfl
      | there entry => exact (congrArg SyntaxSubstitution.shift (hb entry)).trans (shift_encoding (bs entry))
    · intro sort entry
      exact (congrArg SyntaxSubstitution.shift (hf entry)).trans (shift_encoding (fs entry))

/-- 固定原formula变换的首bound槽实例；原始树操作保持两类像的原递归约定。 -/
def instantiateTree (replacement input : Original.Tree) : Original.Tree :=
  SyntaxSubstitution.formula (fun i => match i with | 0 => replacement | j+1 => SyntaxSubstitution.bvar j)
    SyntaxSubstitution.fvar input

theorem instantiate_encoding {bound free : Ctx} (input : Fm (SetSort.set :: bound) free)
    (replacement : Tm bound free) :
    instantiateTree (termTree replacement) (formulaTree input) = formulaTree (input.instantiateTop replacement) := by
  unfold instantiateTree Formula.instantiateTop Formula.substitute Substitution.instantiateTop
  apply formula_substitute
  · intro sort entry
    cases entry <;> rfl
  · intro sort entry
    rfl

theorem abstract_encoding {bound free : Ctx} (input : Fm bound (SetSort.set :: free)) :
    SyntaxSubstitution.abstractTop (formulaTree input) = formulaTree input.abstractFreeTop := by
  unfold SyntaxSubstitution.abstractTop Formula.abstractFreeTop Formula.substitute Substitution.abstractFreeTop
  apply formula_substitute
  · intro sort entry
    rfl
  · intro sort entry
    cases entry <;> rfl

theorem source_instantiate {n} {bound free : Ctx} (ρ : Fin n → Tm bound free)
    (input : Source.Formula (n+1)) (replacement : Fin n) :
    instantiateTree (termTree (ρ replacement)) (formulaTree (Syntax.formula (Syntax.lift ρ) input)) =
      formulaTree (Syntax.formula ρ (input.instantiate replacement)) :=
  (instantiate_encoding (Syntax.formula (Syntax.lift ρ) input) (ρ replacement)).trans
    (congrArg formulaTree (Syntax.instantiate ρ input replacement).symm)

theorem source_fresh_abstract {n} {free : Ctx} (ρ : Fin n → Tm [] free) (input : Source.Formula (n+1)) :
    SyntaxSubstitution.abstractTop (formulaTree (Syntax.formula (Syntax.fresh ρ) input)) =
      formulaTree (Syntax.formula (Syntax.lift ρ) input) :=
  (abstract_encoding (Syntax.formula (Syntax.fresh ρ) input)).trans
    (congrArg formulaTree (Syntax.fresh_abstract ρ input))

end PPAC.Migration.PureSyntaxOperations
