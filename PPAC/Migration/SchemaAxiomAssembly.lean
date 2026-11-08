/- Original YesMetaZFC SchemaTemplate for native ZF's unbounded Separation
and Collection. Reuse the original templates, Expr evaluation and INTERNAL
forall-closure recursion. This is the assembly consumer of already-renamed
matrix codes; the full ZF/U certificate test and Con transport remain separate. -/
import PPAC.Migration.Internal.HornExprExistence
import PPAC.Migration.Internal.HornExprUnique
import PPAC.Migration.Internal.SyntaxUnaryIterationCore
import PPAC.Migration.Internal.ObjectSchemaIndex
import PPAC.Migration.PureSyntaxQuotation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaTemplate

namespace PPAC.Migration.SchemaAxiomAssembly
open Source SourceAlgebra SourceLogic
open PPAC.Migration.Internal
open PPAC.Migration.Internal.HornExprSyntax
open OmegaSyntax
open PPAC.Migration.Internal.SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation.ObjectTreeTemplate (Template)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
attribute [local implicit_reducible] YesMetaZFC.SetTheory.signature
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000

/-- Project membership has two fields; the original pure kernel membership
node has the relation-symbol scalar followed by the two unchanged terms.
The original schema shapes use no other defined atoms. -/
private def pureExpr {a : Nat} : Template a → Expr a
  | .hole i => .var i
  | .leaf t => .node (.literal t) []
  | .unary t x => .node (.literal t) [pureExpr x]
  | .binary t x y => if t = 2 then
      .node (.literal 2) [(.node (.literal 0) []), x.expr, y.expr]
    else .node (.literal t) [pureExpr x,pureExpr y]

/-- Retain the actual original Separation/Collection shell and hole order. -/
def coreProgram (collection : Bool) : Expr 3 :=
  pureExpr (if collection then SchemaTemplate.collection else SchemaTemplate.separation)

def assembled {m} (collection : Bool) (w count : Fin m) (v : Fin 3 → Fin m) (out : Fin m) : Source.Formula m := .ex
  ((Source.Formula.mem (Fin.last m) w.castSucc).conj
    ((graph (coreProgram collection) w.castSucc (fun i => (v i).castSucc) (Fin.last m)).conj
      (SyntaxUnaryIterationSyntax.forallClosure w.castSucc (Fin.last m) count.castSucc out.castSucc)))

def existsOutput {m} (collection : Bool) (w count : Fin m) (v : Fin 3 → Fin m) : Source.Formula m := .ex
  ((Source.Formula.mem (Fin.last m) w.castSucc).conj
    (assembled collection w.castSucc count.castSucc (fun i => (v i).castSucc) (Fin.last m)))

def uniqueOutput {m} (collection : Bool) (w count : Fin m) (v : Fin 3 → Fin m) (out : Fin m) : Source.Formula m := .all
  ((assembled collection w.castSucc count.castSucc (fun i => (v i).castSucc) (Fin.last m)).imp (.equal (Fin.last m) out.castSucc))

def fiber {m} (collection : Bool) (w count : Fin m) (v : Fin 3 → Fin m) : Source.Formula m := .ex
  (((Source.Formula.mem (Fin.last m) w.castSucc).conj
    (assembled collection w.castSucc count.castSucc (fun i => (v i).castSucc) (Fin.last m))).conj
      (uniqueOutput collection w.castSucc count.castSucc (fun i => (v i).castSucc) (Fin.last m)))

theorem assembled_rename {m l} (collection : Bool) (w count out : Fin m) (v : Fin 3 → Fin m) (r : Fin m → Fin l) :
    (assembled collection w count v out).rename r = assembled collection (r w) (r count) (fun i => r (v i)) (r out) := by
  simp only [assembled,Formula.rename,graph_rename,SyntaxUnaryIterationSyntax.forallClosure_rename,
    Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem existsOutput_rename {m l} (collection : Bool) (w count : Fin m) (v : Fin 3 → Fin m) (r : Fin m → Fin l) :
    (existsOutput collection w count v).rename r = existsOutput collection (r w) (r count) (fun i => r (v i)) := by
  simp only [existsOutput,Formula.rename,assembled_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem uniqueOutput_rename {m l} (collection : Bool) (w count out : Fin m) (v : Fin 3 → Fin m) (r : Fin m → Fin l) :
    (uniqueOutput collection w count v out).rename r = uniqueOutput collection (r w) (r count) (fun i => r (v i)) (r out) := by
  simp only [uniqueOutput,Formula.rename,assembled_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem fiber_rename {m l} (collection : Bool) (w count : Fin m) (v : Fin 3 → Fin m) (r : Fin m → Fin l) :
    (fiber collection w count v).rename r = fiber collection (r w) (r count) (fun i => r (v i)) := by
  simp only [fiber,Formula.rename,assembled_rename,uniqueOutput_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

/-- Both actual intermediate code and the whole internal closure are built. -/
theorem output_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (collection : Bool)
    (w count : Fin m) (v : Fin 3 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (Source.Formula.mem count w)) (hv : Derives Γ (environmentNat 3 w v)) :
    Derives Γ (existsOutput collection w count v) := by
  let X := (Source.Formula.mem (Fin.last m) w.castSucc).conj
    (graph (coreProgram collection) w.castSucc (fun i => (v i).castSucc) (Fin.last m))
  let Δ := Context.add X (Context.image Formula.raise Γ)
  apply Derives.exE (p := X) (HornExprExistence.exists_value hZ (coreProgram collection) w v hw hv)
  have hX : Derives Δ X := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw X)
  have hn1 := under hn X
  let Y := (Source.Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (SyntaxUnaryIterationSyntax.forallClosure w.castSucc.castSucc (Fin.last m).castSucc count.castSucc.castSucc (Fin.last (m+1)))
  let Ξ := Context.add Y (Context.image Formula.raise Δ)
  apply Derives.exE (p := Y) (SyntaxUnaryIterationCore.exists_iteration (ZFContext.under hZ X) 9
    w.castSucc (Fin.last m) count.castSucc hw1 (.conjL hX) hn1)
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hX2 : Derives Ξ ((Source.Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj
      (graph (coreProgram collection) w.castSucc.castSucc (fun i => (v i).castSucc.castSucc) (Fin.last m).castSucc)) := by
    simpa only [X,Formula.raise,Formula.rename,graph_rename] using under hX Y
  have ha : Derives Ξ (assembled collection w.castSucc.castSucc count.castSucc.castSucc
      (fun i => (v i).castSucc.castSucc) (Fin.last (m+1))) := by
    apply Derives.exI (Fin.last m).castSucc
    simp only [Formula.instantiate,Formula.rename,graph_rename,SyntaxUnaryIterationSyntax.forallClosure_rename,
      Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
    exact .conjI (.conjL hX2) (.conjI (.conjR hX2) (.conjR hY))
  have ho : Derives Ξ (existsOutput collection w.castSucc.castSucc count.castSucc.castSucc
      (fun i => (v i).castSucc.castSucc)) := by
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Formula.instantiate,Formula.rename,assembled_rename,
      Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI (.conjL hY) ha)
  exact of_eq (by simp only [Formula.raise,existsOutput_rename]) ho

theorem output_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (collection : Bool)
    (w count x y : Fin m) (v : Fin 3 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (Source.Formula.mem count w)) (hv : Derives Γ (environmentNat 3 w v))
    (hx : Derives Γ (assembled collection w count v x)) (hy : Derives Γ (assembled collection w count v y)) :
    Derives Γ (.equal x y) := by
  let X := (Source.Formula.mem (Fin.last m) w.castSucc).conj
    ((graph (coreProgram collection) w.castSucc (fun i => (v i).castSucc) (Fin.last m)).conj
      (SyntaxUnaryIterationSyntax.forallClosure w.castSucc (Fin.last m) count.castSucc x.castSucc))
  let Δ := Context.add X (Context.image Formula.raise Γ)
  apply Derives.exE (p := X) hx
  have hX : Derives Δ X := .hyp (Or.inl rfl)
  have hy1 := of_eq (assembled_rename collection w count y v Fin.castSucc) (under hy X)
  let Y := (Source.Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    ((graph (coreProgram collection) w.castSucc.castSucc (fun i => (v i).castSucc.castSucc) (Fin.last (m+1))).conj
      (SyntaxUnaryIterationSyntax.forallClosure w.castSucc.castSucc (Fin.last (m+1)) count.castSucc.castSucc y.castSucc.castSucc))
  let Ξ := Context.add Y (Context.image Formula.raise Δ)
  apply Derives.exE (p := Y) hy1
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hX2 : Derives Ξ ((Source.Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj
      ((graph (coreProgram collection) w.castSucc.castSucc (fun i => (v i).castSucc.castSucc) (Fin.last m).castSucc).conj
        (SyntaxUnaryIterationSyntax.forallClosure w.castSucc.castSucc (Fin.last m).castSucc count.castSucc.castSucc x.castSucc.castSucc))) := by
    simpa only [X,Formula.raise,Formula.rename,graph_rename,SyntaxUnaryIterationSyntax.forallClosure_rename] using under hX Y
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise,omega_rename]) (under (under hw X) Y)
  have hv2 : Derives Ξ (environmentNat 3 w.castSucc.castSucc (fun i => (v i).castSucc.castSucc)) := of_eq (by simp only [Formula.raise,environmentNat_rename]) (under (under hv X) Y)
  have hn2 : Derives Ξ (Source.Formula.mem count.castSucc.castSucc w.castSucc.castSucc) := by
    simpa only [Formula.raise,Formula.rename] using under (under hn X) Y
  have he := HornExprUnique.unique (ZFContext.under (ZFContext.under hZ X) Y) (coreProgram collection)
    w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (fun i => (v i).castSucc.castSucc)
    hw2 hv2 (.conjL (.conjR hX2)) (.conjL (.conjR hY))
  let P := SyntaxUnaryIterationSyntax.forallClosure w.castSucc.castSucc.castSucc (Fin.last (m+2))
    count.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc
  have h0 : P.instantiate (Fin.last m).castSucc =
      SyntaxUnaryIterationSyntax.forallClosure w.castSucc.castSucc (Fin.last m).castSucc count.castSucc.castSucc x.castSucc.castSucc := by
    simp only [P,Formula.instantiate,SyntaxUnaryIterationSyntax.forallClosure_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate (Fin.last (m+1)) =
      SyntaxUnaryIterationSyntax.forallClosure w.castSucc.castSucc (Fin.last (m+1)) count.castSucc.castSucc x.castSucc.castSucc := by
    simp only [P,Formula.instantiate,SyntaxUnaryIterationSyntax.forallClosure_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have hi := of_eq h1 (Derives.eqSubst P he (of_eq h0.symm (.conjR (.conjR hX2))))
  exact SyntaxUnaryIterationCore.unique (ZFContext.under (ZFContext.under hZ X) Y) 9
    w.castSucc.castSucc (Fin.last (m+1)) count.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc
    hw2 hn2 hi (.conjR (.conjR hY))

theorem output_exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (collection : Bool)
    (w count : Fin m) (v : Fin 3 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (Source.Formula.mem count w)) (hv : Derives Γ (environmentNat 3 w v)) :
    Derives Γ (fiber collection w count v) := by
  let Y := (Source.Formula.mem (Fin.last m) w.castSucc).conj
    (assembled collection w.castSucc count.castSucc (fun i => (v i).castSucc) (Fin.last m))
  let Δ := Context.add Y (Context.image Formula.raise Γ)
  apply Derives.exE (p := Y) (output_exists hZ collection w count v hw hn hv)
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw Y)
  have hv1 := of_eq (environmentNat_rename 3 w v Fin.castSucc) (under hv Y)
  have hu : Derives Δ (uniqueOutput collection w.castSucc count.castSucc (fun i => (v i).castSucc) (Fin.last m)) := by
    apply Derives.allI
    apply Derives.impI
    let E := assembled collection w.castSucc.castSucc count.castSucc.castSucc
      (fun i => (v i).castSucc.castSucc) (Fin.last (m+1))
    have hx2 := of_eq (assembled_rename collection w.castSucc count.castSucc (Fin.last m)
      (fun i => (v i).castSucc) Fin.castSucc) (under (.conjR hY) E)
    exact output_unique (ZFContext.under (ZFContext.under hZ Y) E) collection w.castSucc.castSucc
      count.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc (fun i => (v i).castSucc.castSucc)
      (of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 E))
      (by simpa only [Formula.raise,Formula.rename] using under (under hn Y) E)
      (of_eq (environmentNat_rename 3 w.castSucc (fun i => (v i).castSucc) Fin.castSucc) (under hv1 E))
      (.hyp (Or.inl rfl)) hx2
  have ho : Derives Δ (fiber collection w.castSucc count.castSucc (fun i => (v i).castSucc)) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Y,Formula.instantiate,Formula.rename,assembled_rename,uniqueOutput_rename,
      Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hY hu)
  exact of_eq (fiber_rename collection w count v Fin.castSucc).symm ho

/-- The count is an OBJECT natural; the conclusion includes the actual whole
closure and scalar uniqueness, without a standard-count or trace oracle. -/
def sentence {m} (collection : Bool) (w count : Fin m) (v : Fin 3 → Fin m) : Source.Sentence :=
  ((omega w).imp ((Source.Formula.mem count w).imp ((environmentNat 3 w v).imp (fiber collection w count v)))).close

theorem source_certificate {m} (collection : Bool) (w count : Fin m) (v : Fin 3 → Fin m) :
    Derives (Source.SetLanguage.ZF.at 0) (sentence collection w count v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ := Context.add (environmentNat 3 w v) (Context.add (Source.Formula.mem count w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _
  exact output_exists_unique hZ collection w count v (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem kernel_certificate {m} (collection : Bool) (w count : Fin m) (v : Fin 3 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence collection w count v)) :=
  ZFReplay.replay (TheoryTransport.sentence (source_certificate collection w count v))


private theorem bound_index {n : Nat} (i : Fin n) :
    (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_variable i).index = i.val := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases rfl (fun j => ?_) i
    exact congrArg Nat.succ (ih j)

private abbrev formulaValue {n : Nat}
    (p : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 n) (h : p.FreeClosed) : Nat :=
  YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.IntrinsicQuotation.treeValue
    (PureSyntaxQuotation.formulaTree
      (YesMetaZFC.SetTheory.Definitional.Project.fo_formula p h))

/-- Exact native quotation for EVERY original Separation matrix and scope,
not an example or a replacement schema with weaker quantifiers. -/
theorem separation_quotation {n : Nat}
    (schema : YesMetaZFC.SetTheory.Definitional.Project.UnarySchema n) :
    (coreProgram false).eval (fun _ => formulaValue
      (schema.body.rename YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderTwo)
      (by simpa only [YesMetaZFC.SetTheory.Definitional.Formula.freeClosed_rename] using schema.freeClosed)) =
      formulaValue (YesMetaZFC.SetTheory.Axioms.Schema.separationCore schema)
        (by simp [YesMetaZFC.SetTheory.Axioms.Schema.separationCore,
          YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed,schema.freeClosed]) := by
  simp -implicitDefEqProofs [
    YesMetaZFC.SetTheory.Axioms.Schema.separationCore,
    SchemaTemplate.separation,
    coreProgram,
    pureExpr,
    formulaValue,
    SchemaTemplate.boundTerm,
    SchemaTemplate.member,
    Expr.eval,
    Expr.node,
    PureSyntaxQuotation.formulaTree,
    PureSyntaxQuotation.termTree,
    YesMetaZFC.SetTheory.Definitional.Project.fo_formula,
    YesMetaZFC.SetTheory.Definitional.Project.fo_mem,
    YesMetaZFC.SetTheory.Definitional.Project.fo_term,
    PureSyntaxQuotation.argumentTrees,
    PureSyntaxQuotation.Original.leaf,
    YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf,
    YesMetaZFC.Automation.ObjectHorn.nodeValue,
    YesMetaZFC.Automation.ObjectHorn.listValue,
    Template.expr,
    Expr.list,
    bound_index]

/-- Exact native quotation for EVERY original Collection matrix; both distinct
renamed matrix occurrences and the original bounded-quantifier shell remain. -/
theorem collection_quotation {n : Nat}
    (schema : YesMetaZFC.SetTheory.Definitional.Project.BinarySchema n) :
    (coreProgram true).eval (fun i => if i.val = 0 then formulaValue
      (schema.body.rename YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne)
      (by simpa only [YesMetaZFC.SetTheory.Definitional.Formula.freeClosed_rename] using schema.freeClosed)
      else formulaValue (schema.body.rename YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo)
      (by simpa only [YesMetaZFC.SetTheory.Definitional.Formula.freeClosed_rename] using schema.freeClosed)) =
      formulaValue (YesMetaZFC.SetTheory.Axioms.Schema.collectionCore schema)
        (by simp [YesMetaZFC.SetTheory.Axioms.Schema.collectionCore,
          YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed,
          YesMetaZFC.SetTheory.Definitional.Project.Formula.forallMem,
          YesMetaZFC.SetTheory.Definitional.Project.Formula.existsMem,
          YesMetaZFC.SetTheory.Definitional.Project.Term.newest,schema.freeClosed]) := by
  simp -implicitDefEqProofs [
    YesMetaZFC.SetTheory.Axioms.Schema.collectionCore,
    YesMetaZFC.SetTheory.Definitional.Project.Formula.forallMem,
    YesMetaZFC.SetTheory.Definitional.Project.Formula.existsMem,
    YesMetaZFC.SetTheory.Definitional.Project.Term.newest,
    SchemaTemplate.collection,
    coreProgram,
    pureExpr,
    formulaValue,
    SchemaTemplate.boundTerm,
    SchemaTemplate.member,
    Expr.eval,
    Expr.node,
    PureSyntaxQuotation.formulaTree,
    PureSyntaxQuotation.termTree,
    YesMetaZFC.SetTheory.Definitional.Project.fo_formula,
    YesMetaZFC.SetTheory.Definitional.Project.fo_mem,
    YesMetaZFC.SetTheory.Definitional.Project.fo_term,
    PureSyntaxQuotation.argumentTrees,
    PureSyntaxQuotation.Original.leaf,
    YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf,
    YesMetaZFC.Automation.ObjectHorn.nodeValue,
    YesMetaZFC.Automation.ObjectHorn.listValue,
    YesMetaZFC.SetTheory.Definitional.Term.weaken,
    YesMetaZFC.SetTheory.Definitional.Term.rename,
    Template.expr,
    Expr.list]
  rfl

end PPAC.Migration.SchemaAxiomAssembly
