import PPAC.Migration.SyntaxTransport
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxSubstitution

/-! 原纯成员语法的显式11构造quotation桥。仅为编码接口中间引理，不是内部Con或任意内部码的对象正确性证明。 -/
namespace PPAC.Migration.PureSyntaxQuotation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder
open YesMetaZFC.SetTheory
namespace Original
abbrev Basic := Nonlogical.BasicSetTheory.signature
abbrev GroundSort := Nonlogical.BasicSetTheory.SetSort
abbrev Ctx := List GroundSort
abbrev Tree := FirstOrder.FormalSystem.ProofT.NatPacket.Tree
abbrev leaf := FirstOrder.FormalSystem.ProofT.NatPacket.leaf
end Original
abbrev Ctx := FirstOrder.SortContext ℒ
abbrev Tm (bound free : Ctx) (sort : SetSort := .set) := FirstOrder.Term ℒ bound free sort
abbrev Fm (bound free : Ctx) := FirstOrder.Formula ℒ bound free
attribute [local implicit_reducible] SetTheory.signature

def context : Ctx → Original.Ctx
  | [] => []
  | _ :: tail => .set :: context tail

def embedVariable {scope : Ctx} {sort : SetSort} : Variable scope sort → Variable (context scope) Nonlogical.BasicSetTheory.SetSort.set
  | .here => .here
  | .there entry => .there (embedVariable entry)

theorem variable_index {scope : Ctx} {sort : SetSort} (entry : Variable scope sort) :
    (embedVariable entry).index = entry.index := by
  induction entry with
  | here => rfl
  | there entry ih => exact congrArg (· + 1) ih

def term {bound free : Ctx} {sort : SetSort} : Tm bound free sort →
    FirstOrder.Term Original.Basic (context bound) (context free) Nonlogical.BasicSetTheory.SetSort.set
  | .bvar entry => .bvar (embedVariable entry)
  | .fvar entry => .fvar (embedVariable entry)
  | .app symbol _ => nomatch symbol

def arguments {bound free sorts : Ctx} : FirstOrder.Arguments ℒ bound free sorts →
    FirstOrder.Arguments Original.Basic (context bound) (context free) (context sorts)
  | .nil => .nil
  | .cons head tail => .cons (term head) (arguments tail)

def formula {bound free : Ctx} : Fm bound free → FirstOrder.Formula Original.Basic (context bound) (context free)
  | .falsum => .falsum
  | .truth => .truth
  | .rel .membership args => .rel Nonlogical.BasicSetTheory.RelationSymbol.membership (arguments args)
  | .equal left right => .equal (term left) (term right)
  | .neg body => .neg (formula body)
  | .conj left right => .conj (formula left) (formula right)
  | .disj left right => .disj (formula left) (formula right)
  | .imp left right => .imp (formula left) (formula right)
  | .iff left right => .iff (formula left) (formula right)
  | .forallE _ body => .forallE Nonlogical.BasicSetTheory.SetSort.set (formula body)
  | .existsE _ body => .existsE Nonlogical.BasicSetTheory.SetSort.set (formula body)

def termTree {bound free : Ctx} {sort : SetSort} : Tm bound free sort → Original.Tree
  | .bvar entry => .node 0 [Original.leaf entry.index]
  | .fvar entry => .node 1 [Original.leaf entry.index]
  | .app symbol _ => nomatch symbol

def argumentTrees {bound free sorts : Ctx} : FirstOrder.Arguments ℒ bound free sorts → List Original.Tree
  | .nil => []
  | .cons head tail => termTree head :: argumentTrees tail

def formulaTree {bound free : Ctx} : Fm bound free → Original.Tree
  | .falsum => Original.leaf 0
  | .truth => Original.leaf 1
  | .rel .membership args => .node 2 (Original.leaf 0 :: argumentTrees args)
  | .equal left right => .node 3 [termTree left, termTree right]
  | .neg body => .node 4 [formulaTree body]
  | .conj left right => .node 5 [formulaTree left, formulaTree right]
  | .disj left right => .node 6 [formulaTree left, formulaTree right]
  | .imp left right => .node 7 [formulaTree left, formulaTree right]
  | .iff left right => .node 8 [formulaTree left, formulaTree right]
  | .forallE _ body => .node 9 [formulaTree body]
  | .existsE _ body => .node 10 [formulaTree body]

theorem term_encoding {bound free : Ctx} {sort : SetSort} : (input : Tm bound free sort) →
    FirstOrder.FormalSystem.ProofT.SyntaxEncode.term (term input) = termTree input
  | .bvar entry => by simp only [term, termTree, FirstOrder.FormalSystem.ProofT.SyntaxEncode.term_bvar, variable_index]
  | .fvar entry => by simp only [term, termTree, FirstOrder.FormalSystem.ProofT.SyntaxEncode.term_fvar, variable_index]
  | .app symbol _ => nomatch symbol

theorem arguments_encoding {bound free sorts : Ctx} (input : FirstOrder.Arguments ℒ bound free sorts) :
    FirstOrder.FormalSystem.ProofT.SyntaxEncode.argumentsList (arguments input) = argumentTrees input := by
  cases input with
  | nil => rfl
  | cons head tail => simp only [arguments, argumentTrees, FirstOrder.FormalSystem.ProofT.SyntaxEncode.argumentsList, term_encoding, arguments_encoding tail]
termination_by sizeOf input

theorem formula_encoding {bound free : Ctx} (input : Fm bound free) :
    FirstOrder.FormalSystem.ProofT.SyntaxEncode.formula (formula input) = formulaTree input := by
  induction input with
  | falsum | truth => rfl
  | rel symbol args =>
    cases symbol
    change FirstOrder.FormalSystem.ProofT.NatPacket.Tree.node 2 (Original.leaf 0 :: FirstOrder.FormalSystem.ProofT.SyntaxEncode.argumentsList (arguments args)) = FirstOrder.FormalSystem.ProofT.NatPacket.Tree.node 2 (Original.leaf 0 :: argumentTrees args)
    rw [arguments_encoding args]
  | equal left right => simp only [formula, formulaTree, FirstOrder.FormalSystem.ProofT.SyntaxEncode.formula, term_encoding]
  | neg body ih => simp only [formula, formulaTree, FirstOrder.FormalSystem.ProofT.SyntaxEncode.formula, ih]
  | conj left right ihl ihr | disj left right ihl ihr | imp left right ihl ihr | iff left right ihl ihr =>
    simp only [formula, formulaTree, FirstOrder.FormalSystem.ProofT.SyntaxEncode.formula, ihl, ihr]
  | forallE sort body ih =>
    cases sort
    exact congrArg (fun t => FirstOrder.FormalSystem.ProofT.NatPacket.Tree.node 9 [t]) ih
  | existsE sort body ih =>
    cases sort
    exact congrArg (fun t => FirstOrder.FormalSystem.ProofT.NatPacket.Tree.node 10 [t]) ih

end PPAC.Migration.PureSyntaxQuotation
