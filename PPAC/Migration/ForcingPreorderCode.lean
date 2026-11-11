import PPAC.Migration.ForcingAtomicBasic
import PPAC.Migration.ForcingGuardCode
import PPAC.Migration.ProjectNativeRenaming

/-! The literal original preorder: fixed pinned source AST, not a new preorder
axiom. Its quotation will be opened by the existing mixed substitution engine,
so actual target scopes and condition codes need not be externally standard. -/
namespace PPAC.Migration.ForcingPreorderCode
section Templates
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open SetTheory.Definitional.Project (fo_bound_context fo_bound_variable)
attribute [local implicit_reducible] SetTheory.signature

private def native {k} (input : Source.Formula k) : PureSyntaxQuotation.Fm [] (fo_bound_context k) :=
  (Translation.formula fo_bound_variable input).substituteMapped
    (fun v => .fvar v) (fun {sort} (v : FirstOrder.Variable ([] : FirstOrder.SortContext ℒ) sort) => nomatch v)

def source {n} (R : Source.Formula (n+2)) : Source.Formula (n+2) :=
  ForcingAtomicBasic.preorder R (fun i => i.castSucc.castSucc) (Fin.last n).castSucc

def template {n} (R : Source.Formula (n+2)) : PureSyntaxQuotation.Fm [] (fo_bound_context (n+2)) := native (source R)

private def andLeft {b f : PureSyntaxQuotation.Ctx} : PureSyntaxQuotation.Fm b f → PureSyntaxQuotation.Fm b f
  | .conj p _ => p
  | _ => .truth
private def andRight {b f : PureSyntaxQuotation.Ctx} : PureSyntaxQuotation.Fm b f → PureSyntaxQuotation.Fm b f
  | .conj _ p => p
  | _ => .truth
private def allBody {b f : PureSyntaxQuotation.Ctx} : PureSyntaxQuotation.Fm b f → PureSyntaxQuotation.Fm (SetSort.set :: b) f
  | .forallE .set p => p
  | _ => .truth
private def impLeft {b f : PureSyntaxQuotation.Ctx} : PureSyntaxQuotation.Fm b f → PureSyntaxQuotation.Fm b f
  | .imp p _ => p
  | _ => .truth
private def impRight {b f : PureSyntaxQuotation.Ctx} : PureSyntaxQuotation.Fm b f → PureSyntaxQuotation.Fm b f
  | .imp _ p => p
  | _ => .truth

def reflexive {n} (R : Source.Formula (n+2)) := andLeft (template R)
def reflexiveBody {n} (R : Source.Formula (n+2)) := allBody (reflexive R)

def reflexiveLeaf {n} (R : Source.Formula (n+2)) (order : Bool) :=
  if order then impRight (reflexiveBody R) else impLeft (reflexiveBody R)

def transitive {n} (R : Source.Formula (n+2)) := andRight (template R)
def body1 {n} (R : Source.Formula (n+2)) := allBody (transitive R)
def body2 {n} (R : Source.Formula (n+2)) := allBody (body1 R)
def matrix {n} (R : Source.Formula (n+2)) := allBody (body2 R)
private def t1 {n} (R : Source.Formula (n+2)) := impRight (matrix R)
private def t2 {n} (R : Source.Formula (n+2)) := impRight (t1 R)
private def t3 {n} (R : Source.Formula (n+2)) := impRight (t2 R)
private def t4 {n} (R : Source.Formula (n+2)) := impRight (t3 R)
def tails {n} (R : Source.Formula (n+2)) : Fin 5 → PureSyntaxQuotation.Fm [SetSort.set,SetSort.set,SetSort.set] (fo_bound_context (n+2)) :=
  Fin.cases (matrix R) (Fin.cases (t1 R) (Fin.cases (t2 R) (Fin.cases (t3 R) (fun _ => t4 R))))
def atoms {n} (R : Source.Formula (n+2)) : Fin 6 → PureSyntaxQuotation.Fm [SetSort.set,SetSort.set,SetSort.set] (fo_bound_context (n+2)) :=
  Fin.cases (impLeft (matrix R)) (Fin.cases (impLeft (t1 R)) (Fin.cases (impLeft (t2 R)) (Fin.cases (impLeft (t3 R)) (Fin.cases (impLeft (t4 R)) (fun _ => impRight (t4 R))))))

theorem template_conjunction {n} (R : Source.Formula (n+2)) : template R = .conj (reflexive R) (transitive R) := rfl
theorem transitive_all {n} (R : Source.Formula (n+2)) : transitive R = .forallE .set (body1 R) := rfl
theorem body1_all {n} (R : Source.Formula (n+2)) : body1 R = .forallE .set (body2 R) := rfl
theorem body2_all {n} (R : Source.Formula (n+2)) : body2 R = .forallE .set (matrix R) := rfl
theorem matrix_implications {n} (R : Source.Formula (n+2)) : matrix R =
    .imp (atoms R 0) (.imp (atoms R 1) (.imp (atoms R 2) (.imp (atoms R 3) (.imp (atoms R 4) (atoms R 5))))) := rfl

end Templates

open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open PureQuotationTypedSyntax (formulaValue formulaValue_rename)
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
attribute [local irreducible] NaturalRecursionSyntax.matrix

private theorem quoted_conj {m} {Γ : Context m} {b f : PureSyntaxQuotation.Ctx}
    (hZ : ZFContext.Evidence Γ) (left right : PureSyntaxQuotation.Fm b f) (w n x y : Fin m)
    (hw : Derives Γ (omega w))
    (hn : Derives Γ (PureQuotationSyntax.formula (.conj left right) w n))
    (hx : Derives Γ (PureQuotationSyntax.formula left w x)) (hy : Derives Γ (PureQuotationSyntax.formula right w y)) :
    Derives Γ (SyntaxLogicalSyntax.binaryCode 0 w x y n) := by
  exact OriginalQuotationNodeFields.tree_to_constructor hZ 5 [PureSyntaxQuotation.formulaTree left,PureSyntaxQuotation.formulaTree right]
    w n (SyntaxAtomSyntax.two x y) hw (.conjI hx (.conjI hy (.eqRefl w))) hn

private theorem quoted_imp {m} {Γ : Context m} {b f : PureSyntaxQuotation.Ctx}
    (hZ : ZFContext.Evidence Γ) (left right : PureSyntaxQuotation.Fm b f) (w n x y : Fin m)
    (hw : Derives Γ (omega w))
    (hn : Derives Γ (PureQuotationSyntax.formula (.imp left right) w n))
    (hx : Derives Γ (PureQuotationSyntax.formula left w x)) (hy : Derives Γ (PureQuotationSyntax.formula right w y)) :
    Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w x y n) := by
  exact OriginalQuotationNodeFields.tree_to_constructor hZ 7 [PureSyntaxQuotation.formulaTree left,PureSyntaxQuotation.formulaTree right]
    w n (SyntaxAtomSyntax.two x y) hw (.conjI hx (.conjI hy (.eqRefl w))) hn

private theorem quoted_all {m} {Γ : Context m} {b f : PureSyntaxQuotation.Ctx}
    (hZ : ZFContext.Evidence Γ) (body : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: b) f) (w n x : Fin m)
    (hw : Derives Γ (omega w))
    (hn : Derives Γ (PureQuotationSyntax.formula (.forallE .set body) w n))
    (hx : Derives Γ (PureQuotationSyntax.formula body w x)) :
    Derives Γ (SyntaxLogicalSyntax.singleCode 9 w x n) := by
  exact OriginalQuotationNodeFields.tree_to_constructor hZ 9 [PureSyntaxQuotation.formulaTree body]
    w n (fun _ => x) hw (.conjI hx (.eqRefl w)) hn

/-- The universal and implication fields of the original reflexivity quote. -/
theorem reflexive_fields {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (w r body member order : Fin m) (hw : Derives Γ (omega w))
    (hr : Derives Γ (PureQuotationSyntax.formula (reflexive R) w r))
    (hb : Derives Γ (PureQuotationSyntax.formula (reflexiveBody R) w body))
    (hm : Derives Γ (PureQuotationSyntax.formula (reflexiveLeaf R false) w member))
    (ho : Derives Γ (PureQuotationSyntax.formula (reflexiveLeaf R true) w order)) :
    Derives Γ ((SyntaxLogicalSyntax.singleCode 9 w body r).conj
      (SyntaxLogicalSyntax.binaryCode 2 w member order body)) :=
  .conjI (quoted_all hZ (reflexiveBody R) w r body hw hr hb)
    (quoted_imp hZ (reflexiveLeaf R false) (reflexiveLeaf R true) w body member order hw hb hm ho)

def rawData {n m} (R : Source.Formula (n+2)) (w z A1 A2 A3 f : Fin m) (v : Fin 16 → Fin m) : Formula m :=
  (formulaValue (template R) w z f (v 0)).conj ((formulaValue (reflexive R) w z f (v 1)).conj ((formulaValue (transitive R) w z f (v 2)).conj ((formulaValue (body1 R) w A1 f (v 3)).conj ((formulaValue (body2 R) w A2 f (v 4)).conj ((formulaValue (tails R 0) w A3 f (v 5)).conj ((formulaValue (tails R 1) w A3 f (v 6)).conj ((formulaValue (tails R 2) w A3 f (v 7)).conj ((formulaValue (tails R 3) w A3 f (v 8)).conj ((formulaValue (tails R 4) w A3 f (v 9)).conj ((formulaValue (atoms R 0) w A3 f (v 10)).conj ((formulaValue (atoms R 1) w A3 f (v 11)).conj ((formulaValue (atoms R 2) w A3 f (v 12)).conj ((formulaValue (atoms R 3) w A3 f (v 13)).conj ((formulaValue (atoms R 4) w A3 f (v 14)).conj ((formulaValue (atoms R 5) w A3 f (v 15)).conj ((SyntaxLogicalSyntax.binaryCode 0 w (v 1) (v 2) (v 0)).conj ((SyntaxLogicalSyntax.singleCode 9 w (v 3) (v 2)).conj ((SyntaxLogicalSyntax.singleCode 9 w (v 4) (v 3)).conj ((SyntaxLogicalSyntax.singleCode 9 w (v 5) (v 4)).conj ((SyntaxLogicalSyntax.binaryCode 2 w (v 10) (v 6) (v 5)).conj ((SyntaxLogicalSyntax.binaryCode 2 w (v 11) (v 7) (v 6)).conj ((SyntaxLogicalSyntax.binaryCode 2 w (v 12) (v 8) (v 7)).conj ((SyntaxLogicalSyntax.binaryCode 2 w (v 13) (v 9) (v 8)).conj ((SyntaxLogicalSyntax.binaryCode 2 w (v 14) (v 15) (v 9))))))))))))))))))))))))))

theorem rawData_rename {n m k} (R : Source.Formula (n+2)) (w z A1 A2 A3 f : Fin m) (v : Fin 16 → Fin m) (ρ : Fin m → Fin k) :
    (rawData R w z A1 A2 A3 f v).rename ρ = rawData R (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ A3) (ρ f) (fun i => ρ (v i)) := by
  simp only [rawData, Formula.rename, formulaValue_rename, SyntaxLogicalSyntax.binaryCode_rename, SyntaxLogicalSyntax.singleCode_rename]

def rawBody {n m} (R : Source.Formula (n+2)) (w z A1 A2 A3 f : Fin m) : Formula (m+16) :=
  rawData R (old 16 w) (old 16 z) (old 16 A1) (old 16 A2) (old 16 A3) (old 16 f) (slot 16)
def rawExists {n m} (R : Source.Formula (n+2)) (w z A1 A2 A3 f : Fin m) : Formula m := existsMany 16 (rawBody R w z A1 A2 A3 f)

theorem rawExists_rename {n m k} (R : Source.Formula (n+2)) (w z A1 A2 A3 f : Fin m) (ρ : Fin m → Fin k) :
    (rawExists R w z A1 A2 A3 f).rename ρ = rawExists R (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ A3) (ρ f) := by
  simp only [rawExists, existsMany_rename, rawBody, rawData_rename, lift_old, lift_slot]

private theorem produce_16 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w z A1 A2 A3 f : Fin m) (v : Fin 16 → Fin m) (hw : Derives Γ (omega w))
    (_h0 : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (_h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (_h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (_h3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (_hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (q0 : Derives Γ (formulaValue (template R) w z f (v 0)))
    (q1 : Derives Γ (formulaValue (reflexive R) w z f (v 1)))
    (q2 : Derives Γ (formulaValue (transitive R) w z f (v 2)))
    (q3 : Derives Γ (formulaValue (body1 R) w A1 f (v 3)))
    (q4 : Derives Γ (formulaValue (body2 R) w A2 f (v 4)))
    (q5 : Derives Γ (formulaValue (tails R 0) w A3 f (v 5)))
    (q6 : Derives Γ (formulaValue (tails R 1) w A3 f (v 6)))
    (q7 : Derives Γ (formulaValue (tails R 2) w A3 f (v 7)))
    (q8 : Derives Γ (formulaValue (tails R 3) w A3 f (v 8)))
    (q9 : Derives Γ (formulaValue (tails R 4) w A3 f (v 9)))
    (q10 : Derives Γ (formulaValue (atoms R 0) w A3 f (v 10)))
    (q11 : Derives Γ (formulaValue (atoms R 1) w A3 f (v 11)))
    (q12 : Derives Γ (formulaValue (atoms R 2) w A3 f (v 12)))
    (q13 : Derives Γ (formulaValue (atoms R 3) w A3 f (v 13)))
    (q14 : Derives Γ (formulaValue (atoms R 4) w A3 f (v 14)))
    (q15 : Derives Γ (formulaValue (atoms R 5) w A3 f (v 15)))
    : Derives Γ (rawExists R w z A1 A2 A3 f) := by
  have c0 := quoted_conj hZ (reflexive R) (transitive R) w (v 0) (v 1) (v 2) hw (.conjL q0) (.conjL q1) (.conjL q2)
  have c1 := quoted_all hZ (body1 R) w (v 2) (v 3) hw (.conjL q2) (.conjL q3)
  have c2 := quoted_all hZ (body2 R) w (v 3) (v 4) hw (.conjL q3) (.conjL q4)
  have c3 := quoted_all hZ (matrix R) w (v 4) (v 5) hw (.conjL q4) (.conjL q5)
  have c4 := quoted_imp hZ (atoms R 0) (tails R 1) w (v 5) (v 10) (v 6) hw (.conjL q5) (.conjL q10) (.conjL q6)
  have c5 := quoted_imp hZ (atoms R 1) (tails R 2) w (v 6) (v 11) (v 7) hw (.conjL q6) (.conjL q11) (.conjL q7)
  have c6 := quoted_imp hZ (atoms R 2) (tails R 3) w (v 7) (v 12) (v 8) hw (.conjL q7) (.conjL q12) (.conjL q8)
  have c7 := quoted_imp hZ (atoms R 3) (tails R 4) w (v 8) (v 13) (v 9) hw (.conjL q8) (.conjL q13) (.conjL q9)
  have c8 := quoted_imp hZ (atoms R 4) (atoms R 5) w (v 9) (v 14) (v 15) hw (.conjL q9) (.conjL q14) (.conjL q15)
  apply HornBinderRules.intro_many 16 _ v
  exact of_eq (by simp only [rawBody, rawData_rename, assign_old, assign_slot]; rfl) (.conjI q0 (.conjI q1 (.conjI q2 (.conjI q3 (.conjI q4 (.conjI q5 (.conjI q6 (.conjI q7 (.conjI q8 (.conjI q9 (.conjI q10 (.conjI q11 (.conjI q12 (.conjI q13 (.conjI q14 (.conjI q15 (.conjI c0 (.conjI c1 (.conjI c2 (.conjI c3 (.conjI c4 (.conjI c5 (.conjI c6 (.conjI c7 c8))))))))))))))))))))))))

private theorem produce_15 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w z A1 A2 A3 f : Fin m) (v : Fin 16 → Fin m) (hw : Derives Γ (omega w))
    (h0 : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (h3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (q0 : Derives Γ (formulaValue (template R) w z f (v 0)))
    (q1 : Derives Γ (formulaValue (reflexive R) w z f (v 1)))
    (q2 : Derives Γ (formulaValue (transitive R) w z f (v 2)))
    (q3 : Derives Γ (formulaValue (body1 R) w A1 f (v 3)))
    (q4 : Derives Γ (formulaValue (body2 R) w A2 f (v 4)))
    (q5 : Derives Γ (formulaValue (tails R 0) w A3 f (v 5)))
    (q6 : Derives Γ (formulaValue (tails R 1) w A3 f (v 6)))
    (q7 : Derives Γ (formulaValue (tails R 2) w A3 f (v 7)))
    (q8 : Derives Γ (formulaValue (tails R 3) w A3 f (v 8)))
    (q9 : Derives Γ (formulaValue (tails R 4) w A3 f (v 9)))
    (q10 : Derives Γ (formulaValue (atoms R 0) w A3 f (v 10)))
    (q11 : Derives Γ (formulaValue (atoms R 1) w A3 f (v 11)))
    (q12 : Derives Γ (formulaValue (atoms R 2) w A3 f (v 12)))
    (q13 : Derives Γ (formulaValue (atoms R 3) w A3 f (v 13)))
    (q14 : Derives Γ (formulaValue (atoms R 4) w A3 f (v 14)))
    : Derives Γ (rawExists R w z A1 A2 A3 f) := by
  have hFree : Derives Γ (SyntaxNumeralSyntax.numeral (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length f) :=
    of_eq (congrArg (fun t => SyntaxNumeralSyntax.numeral t f) (show (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length = n+2 from List.length_replicate).symm) hf
  let E := formulaValue (atoms R 5) w.castSucc A3.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (PureQuotationTypedFormulas.exists_typed hZ (atoms R 5) w A3 f hw h3 hFree)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  let V : Fin 16 → Fin (m+1) := fun j => if j = 15 then Fin.last m else (v j).castSucc
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have h01 := of_eq (SyntaxNumeralSyntax.numeral_rename 0 z Fin.castSucc) (under h0 E)
  have h11 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 A1 Fin.castSucc) (under h1 E)
  have h21 := of_eq (SyntaxNumeralSyntax.numeral_rename 2 A2 Fin.castSucc) (under h2 E)
  have h31 := of_eq (SyntaxNumeralSyntax.numeral_rename 3 A3 Fin.castSucc) (under h3 E)
  have hf1 := of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f Fin.castSucc) (under hf E)
  have raisedQ0 : Derives Δ (formulaValue (template R) w.castSucc z.castSucc f.castSucc (V 0)) := of_eq (formulaValue_rename (template R) w z f (v 0) Fin.castSucc) (under q0 E)
  have raisedQ1 : Derives Δ (formulaValue (reflexive R) w.castSucc z.castSucc f.castSucc (V 1)) := of_eq (formulaValue_rename (reflexive R) w z f (v 1) Fin.castSucc) (under q1 E)
  have raisedQ2 : Derives Δ (formulaValue (transitive R) w.castSucc z.castSucc f.castSucc (V 2)) := of_eq (formulaValue_rename (transitive R) w z f (v 2) Fin.castSucc) (under q2 E)
  have raisedQ3 : Derives Δ (formulaValue (body1 R) w.castSucc A1.castSucc f.castSucc (V 3)) := of_eq (formulaValue_rename (body1 R) w A1 f (v 3) Fin.castSucc) (under q3 E)
  have raisedQ4 : Derives Δ (formulaValue (body2 R) w.castSucc A2.castSucc f.castSucc (V 4)) := of_eq (formulaValue_rename (body2 R) w A2 f (v 4) Fin.castSucc) (under q4 E)
  have raisedQ5 : Derives Δ (formulaValue (tails R 0) w.castSucc A3.castSucc f.castSucc (V 5)) := of_eq (formulaValue_rename (tails R 0) w A3 f (v 5) Fin.castSucc) (under q5 E)
  have raisedQ6 : Derives Δ (formulaValue (tails R 1) w.castSucc A3.castSucc f.castSucc (V 6)) := of_eq (formulaValue_rename (tails R 1) w A3 f (v 6) Fin.castSucc) (under q6 E)
  have raisedQ7 : Derives Δ (formulaValue (tails R 2) w.castSucc A3.castSucc f.castSucc (V 7)) := of_eq (formulaValue_rename (tails R 2) w A3 f (v 7) Fin.castSucc) (under q7 E)
  have raisedQ8 : Derives Δ (formulaValue (tails R 3) w.castSucc A3.castSucc f.castSucc (V 8)) := of_eq (formulaValue_rename (tails R 3) w A3 f (v 8) Fin.castSucc) (under q8 E)
  have raisedQ9 : Derives Δ (formulaValue (tails R 4) w.castSucc A3.castSucc f.castSucc (V 9)) := of_eq (formulaValue_rename (tails R 4) w A3 f (v 9) Fin.castSucc) (under q9 E)
  have raisedQ10 : Derives Δ (formulaValue (atoms R 0) w.castSucc A3.castSucc f.castSucc (V 10)) := of_eq (formulaValue_rename (atoms R 0) w A3 f (v 10) Fin.castSucc) (under q10 E)
  have raisedQ11 : Derives Δ (formulaValue (atoms R 1) w.castSucc A3.castSucc f.castSucc (V 11)) := of_eq (formulaValue_rename (atoms R 1) w A3 f (v 11) Fin.castSucc) (under q11 E)
  have raisedQ12 : Derives Δ (formulaValue (atoms R 2) w.castSucc A3.castSucc f.castSucc (V 12)) := of_eq (formulaValue_rename (atoms R 2) w A3 f (v 12) Fin.castSucc) (under q12 E)
  have raisedQ13 : Derives Δ (formulaValue (atoms R 3) w.castSucc A3.castSucc f.castSucc (V 13)) := of_eq (formulaValue_rename (atoms R 3) w A3 f (v 13) Fin.castSucc) (under q13 E)
  have raisedQ14 : Derives Δ (formulaValue (atoms R 4) w.castSucc A3.castSucc f.castSucc (V 14)) := of_eq (formulaValue_rename (atoms R 4) w A3 f (v 14) Fin.castSucc) (under q14 E)
  have hout := produce_16 (ZFContext.under hZ E) R w.castSucc z.castSucc A1.castSucc A2.castSucc A3.castSucc f.castSucc V hw1 h01 h11 h21 h31 hf1
    raisedQ0
    raisedQ1
    raisedQ2
    raisedQ3
    raisedQ4
    raisedQ5
    raisedQ6
    raisedQ7
    raisedQ8
    raisedQ9
    raisedQ10
    raisedQ11
    raisedQ12
    raisedQ13
    raisedQ14
    hE
  exact of_eq (rawExists_rename R w z A1 A2 A3 f Fin.castSucc).symm hout

private theorem produce_14 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w z A1 A2 A3 f : Fin m) (v : Fin 16 → Fin m) (hw : Derives Γ (omega w))
    (h0 : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (h3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (q0 : Derives Γ (formulaValue (template R) w z f (v 0)))
    (q1 : Derives Γ (formulaValue (reflexive R) w z f (v 1)))
    (q2 : Derives Γ (formulaValue (transitive R) w z f (v 2)))
    (q3 : Derives Γ (formulaValue (body1 R) w A1 f (v 3)))
    (q4 : Derives Γ (formulaValue (body2 R) w A2 f (v 4)))
    (q5 : Derives Γ (formulaValue (tails R 0) w A3 f (v 5)))
    (q6 : Derives Γ (formulaValue (tails R 1) w A3 f (v 6)))
    (q7 : Derives Γ (formulaValue (tails R 2) w A3 f (v 7)))
    (q8 : Derives Γ (formulaValue (tails R 3) w A3 f (v 8)))
    (q9 : Derives Γ (formulaValue (tails R 4) w A3 f (v 9)))
    (q10 : Derives Γ (formulaValue (atoms R 0) w A3 f (v 10)))
    (q11 : Derives Γ (formulaValue (atoms R 1) w A3 f (v 11)))
    (q12 : Derives Γ (formulaValue (atoms R 2) w A3 f (v 12)))
    (q13 : Derives Γ (formulaValue (atoms R 3) w A3 f (v 13)))
    : Derives Γ (rawExists R w z A1 A2 A3 f) := by
  have hFree : Derives Γ (SyntaxNumeralSyntax.numeral (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length f) :=
    of_eq (congrArg (fun t => SyntaxNumeralSyntax.numeral t f) (show (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length = n+2 from List.length_replicate).symm) hf
  let E := formulaValue (atoms R 4) w.castSucc A3.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (PureQuotationTypedFormulas.exists_typed hZ (atoms R 4) w A3 f hw h3 hFree)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  let V : Fin 16 → Fin (m+1) := fun j => if j = 14 then Fin.last m else (v j).castSucc
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have h01 := of_eq (SyntaxNumeralSyntax.numeral_rename 0 z Fin.castSucc) (under h0 E)
  have h11 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 A1 Fin.castSucc) (under h1 E)
  have h21 := of_eq (SyntaxNumeralSyntax.numeral_rename 2 A2 Fin.castSucc) (under h2 E)
  have h31 := of_eq (SyntaxNumeralSyntax.numeral_rename 3 A3 Fin.castSucc) (under h3 E)
  have hf1 := of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f Fin.castSucc) (under hf E)
  have raisedQ0 : Derives Δ (formulaValue (template R) w.castSucc z.castSucc f.castSucc (V 0)) := of_eq (formulaValue_rename (template R) w z f (v 0) Fin.castSucc) (under q0 E)
  have raisedQ1 : Derives Δ (formulaValue (reflexive R) w.castSucc z.castSucc f.castSucc (V 1)) := of_eq (formulaValue_rename (reflexive R) w z f (v 1) Fin.castSucc) (under q1 E)
  have raisedQ2 : Derives Δ (formulaValue (transitive R) w.castSucc z.castSucc f.castSucc (V 2)) := of_eq (formulaValue_rename (transitive R) w z f (v 2) Fin.castSucc) (under q2 E)
  have raisedQ3 : Derives Δ (formulaValue (body1 R) w.castSucc A1.castSucc f.castSucc (V 3)) := of_eq (formulaValue_rename (body1 R) w A1 f (v 3) Fin.castSucc) (under q3 E)
  have raisedQ4 : Derives Δ (formulaValue (body2 R) w.castSucc A2.castSucc f.castSucc (V 4)) := of_eq (formulaValue_rename (body2 R) w A2 f (v 4) Fin.castSucc) (under q4 E)
  have raisedQ5 : Derives Δ (formulaValue (tails R 0) w.castSucc A3.castSucc f.castSucc (V 5)) := of_eq (formulaValue_rename (tails R 0) w A3 f (v 5) Fin.castSucc) (under q5 E)
  have raisedQ6 : Derives Δ (formulaValue (tails R 1) w.castSucc A3.castSucc f.castSucc (V 6)) := of_eq (formulaValue_rename (tails R 1) w A3 f (v 6) Fin.castSucc) (under q6 E)
  have raisedQ7 : Derives Δ (formulaValue (tails R 2) w.castSucc A3.castSucc f.castSucc (V 7)) := of_eq (formulaValue_rename (tails R 2) w A3 f (v 7) Fin.castSucc) (under q7 E)
  have raisedQ8 : Derives Δ (formulaValue (tails R 3) w.castSucc A3.castSucc f.castSucc (V 8)) := of_eq (formulaValue_rename (tails R 3) w A3 f (v 8) Fin.castSucc) (under q8 E)
  have raisedQ9 : Derives Δ (formulaValue (tails R 4) w.castSucc A3.castSucc f.castSucc (V 9)) := of_eq (formulaValue_rename (tails R 4) w A3 f (v 9) Fin.castSucc) (under q9 E)
  have raisedQ10 : Derives Δ (formulaValue (atoms R 0) w.castSucc A3.castSucc f.castSucc (V 10)) := of_eq (formulaValue_rename (atoms R 0) w A3 f (v 10) Fin.castSucc) (under q10 E)
  have raisedQ11 : Derives Δ (formulaValue (atoms R 1) w.castSucc A3.castSucc f.castSucc (V 11)) := of_eq (formulaValue_rename (atoms R 1) w A3 f (v 11) Fin.castSucc) (under q11 E)
  have raisedQ12 : Derives Δ (formulaValue (atoms R 2) w.castSucc A3.castSucc f.castSucc (V 12)) := of_eq (formulaValue_rename (atoms R 2) w A3 f (v 12) Fin.castSucc) (under q12 E)
  have raisedQ13 : Derives Δ (formulaValue (atoms R 3) w.castSucc A3.castSucc f.castSucc (V 13)) := of_eq (formulaValue_rename (atoms R 3) w A3 f (v 13) Fin.castSucc) (under q13 E)
  have hout := produce_15 (ZFContext.under hZ E) R w.castSucc z.castSucc A1.castSucc A2.castSucc A3.castSucc f.castSucc V hw1 h01 h11 h21 h31 hf1
    raisedQ0
    raisedQ1
    raisedQ2
    raisedQ3
    raisedQ4
    raisedQ5
    raisedQ6
    raisedQ7
    raisedQ8
    raisedQ9
    raisedQ10
    raisedQ11
    raisedQ12
    raisedQ13
    hE
  exact of_eq (rawExists_rename R w z A1 A2 A3 f Fin.castSucc).symm hout

private theorem produce_13 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w z A1 A2 A3 f : Fin m) (v : Fin 16 → Fin m) (hw : Derives Γ (omega w))
    (h0 : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (h3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (q0 : Derives Γ (formulaValue (template R) w z f (v 0)))
    (q1 : Derives Γ (formulaValue (reflexive R) w z f (v 1)))
    (q2 : Derives Γ (formulaValue (transitive R) w z f (v 2)))
    (q3 : Derives Γ (formulaValue (body1 R) w A1 f (v 3)))
    (q4 : Derives Γ (formulaValue (body2 R) w A2 f (v 4)))
    (q5 : Derives Γ (formulaValue (tails R 0) w A3 f (v 5)))
    (q6 : Derives Γ (formulaValue (tails R 1) w A3 f (v 6)))
    (q7 : Derives Γ (formulaValue (tails R 2) w A3 f (v 7)))
    (q8 : Derives Γ (formulaValue (tails R 3) w A3 f (v 8)))
    (q9 : Derives Γ (formulaValue (tails R 4) w A3 f (v 9)))
    (q10 : Derives Γ (formulaValue (atoms R 0) w A3 f (v 10)))
    (q11 : Derives Γ (formulaValue (atoms R 1) w A3 f (v 11)))
    (q12 : Derives Γ (formulaValue (atoms R 2) w A3 f (v 12)))
    : Derives Γ (rawExists R w z A1 A2 A3 f) := by
  have hFree : Derives Γ (SyntaxNumeralSyntax.numeral (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length f) :=
    of_eq (congrArg (fun t => SyntaxNumeralSyntax.numeral t f) (show (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length = n+2 from List.length_replicate).symm) hf
  let E := formulaValue (atoms R 3) w.castSucc A3.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (PureQuotationTypedFormulas.exists_typed hZ (atoms R 3) w A3 f hw h3 hFree)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  let V : Fin 16 → Fin (m+1) := fun j => if j = 13 then Fin.last m else (v j).castSucc
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have h01 := of_eq (SyntaxNumeralSyntax.numeral_rename 0 z Fin.castSucc) (under h0 E)
  have h11 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 A1 Fin.castSucc) (under h1 E)
  have h21 := of_eq (SyntaxNumeralSyntax.numeral_rename 2 A2 Fin.castSucc) (under h2 E)
  have h31 := of_eq (SyntaxNumeralSyntax.numeral_rename 3 A3 Fin.castSucc) (under h3 E)
  have hf1 := of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f Fin.castSucc) (under hf E)
  have raisedQ0 : Derives Δ (formulaValue (template R) w.castSucc z.castSucc f.castSucc (V 0)) := of_eq (formulaValue_rename (template R) w z f (v 0) Fin.castSucc) (under q0 E)
  have raisedQ1 : Derives Δ (formulaValue (reflexive R) w.castSucc z.castSucc f.castSucc (V 1)) := of_eq (formulaValue_rename (reflexive R) w z f (v 1) Fin.castSucc) (under q1 E)
  have raisedQ2 : Derives Δ (formulaValue (transitive R) w.castSucc z.castSucc f.castSucc (V 2)) := of_eq (formulaValue_rename (transitive R) w z f (v 2) Fin.castSucc) (under q2 E)
  have raisedQ3 : Derives Δ (formulaValue (body1 R) w.castSucc A1.castSucc f.castSucc (V 3)) := of_eq (formulaValue_rename (body1 R) w A1 f (v 3) Fin.castSucc) (under q3 E)
  have raisedQ4 : Derives Δ (formulaValue (body2 R) w.castSucc A2.castSucc f.castSucc (V 4)) := of_eq (formulaValue_rename (body2 R) w A2 f (v 4) Fin.castSucc) (under q4 E)
  have raisedQ5 : Derives Δ (formulaValue (tails R 0) w.castSucc A3.castSucc f.castSucc (V 5)) := of_eq (formulaValue_rename (tails R 0) w A3 f (v 5) Fin.castSucc) (under q5 E)
  have raisedQ6 : Derives Δ (formulaValue (tails R 1) w.castSucc A3.castSucc f.castSucc (V 6)) := of_eq (formulaValue_rename (tails R 1) w A3 f (v 6) Fin.castSucc) (under q6 E)
  have raisedQ7 : Derives Δ (formulaValue (tails R 2) w.castSucc A3.castSucc f.castSucc (V 7)) := of_eq (formulaValue_rename (tails R 2) w A3 f (v 7) Fin.castSucc) (under q7 E)
  have raisedQ8 : Derives Δ (formulaValue (tails R 3) w.castSucc A3.castSucc f.castSucc (V 8)) := of_eq (formulaValue_rename (tails R 3) w A3 f (v 8) Fin.castSucc) (under q8 E)
  have raisedQ9 : Derives Δ (formulaValue (tails R 4) w.castSucc A3.castSucc f.castSucc (V 9)) := of_eq (formulaValue_rename (tails R 4) w A3 f (v 9) Fin.castSucc) (under q9 E)
  have raisedQ10 : Derives Δ (formulaValue (atoms R 0) w.castSucc A3.castSucc f.castSucc (V 10)) := of_eq (formulaValue_rename (atoms R 0) w A3 f (v 10) Fin.castSucc) (under q10 E)
  have raisedQ11 : Derives Δ (formulaValue (atoms R 1) w.castSucc A3.castSucc f.castSucc (V 11)) := of_eq (formulaValue_rename (atoms R 1) w A3 f (v 11) Fin.castSucc) (under q11 E)
  have raisedQ12 : Derives Δ (formulaValue (atoms R 2) w.castSucc A3.castSucc f.castSucc (V 12)) := of_eq (formulaValue_rename (atoms R 2) w A3 f (v 12) Fin.castSucc) (under q12 E)
  have hout := produce_14 (ZFContext.under hZ E) R w.castSucc z.castSucc A1.castSucc A2.castSucc A3.castSucc f.castSucc V hw1 h01 h11 h21 h31 hf1
    raisedQ0
    raisedQ1
    raisedQ2
    raisedQ3
    raisedQ4
    raisedQ5
    raisedQ6
    raisedQ7
    raisedQ8
    raisedQ9
    raisedQ10
    raisedQ11
    raisedQ12
    hE
  exact of_eq (rawExists_rename R w z A1 A2 A3 f Fin.castSucc).symm hout

private theorem produce_12 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w z A1 A2 A3 f : Fin m) (v : Fin 16 → Fin m) (hw : Derives Γ (omega w))
    (h0 : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (h3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (q0 : Derives Γ (formulaValue (template R) w z f (v 0)))
    (q1 : Derives Γ (formulaValue (reflexive R) w z f (v 1)))
    (q2 : Derives Γ (formulaValue (transitive R) w z f (v 2)))
    (q3 : Derives Γ (formulaValue (body1 R) w A1 f (v 3)))
    (q4 : Derives Γ (formulaValue (body2 R) w A2 f (v 4)))
    (q5 : Derives Γ (formulaValue (tails R 0) w A3 f (v 5)))
    (q6 : Derives Γ (formulaValue (tails R 1) w A3 f (v 6)))
    (q7 : Derives Γ (formulaValue (tails R 2) w A3 f (v 7)))
    (q8 : Derives Γ (formulaValue (tails R 3) w A3 f (v 8)))
    (q9 : Derives Γ (formulaValue (tails R 4) w A3 f (v 9)))
    (q10 : Derives Γ (formulaValue (atoms R 0) w A3 f (v 10)))
    (q11 : Derives Γ (formulaValue (atoms R 1) w A3 f (v 11)))
    : Derives Γ (rawExists R w z A1 A2 A3 f) := by
  have hFree : Derives Γ (SyntaxNumeralSyntax.numeral (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length f) :=
    of_eq (congrArg (fun t => SyntaxNumeralSyntax.numeral t f) (show (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length = n+2 from List.length_replicate).symm) hf
  let E := formulaValue (atoms R 2) w.castSucc A3.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (PureQuotationTypedFormulas.exists_typed hZ (atoms R 2) w A3 f hw h3 hFree)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  let V : Fin 16 → Fin (m+1) := fun j => if j = 12 then Fin.last m else (v j).castSucc
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have h01 := of_eq (SyntaxNumeralSyntax.numeral_rename 0 z Fin.castSucc) (under h0 E)
  have h11 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 A1 Fin.castSucc) (under h1 E)
  have h21 := of_eq (SyntaxNumeralSyntax.numeral_rename 2 A2 Fin.castSucc) (under h2 E)
  have h31 := of_eq (SyntaxNumeralSyntax.numeral_rename 3 A3 Fin.castSucc) (under h3 E)
  have hf1 := of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f Fin.castSucc) (under hf E)
  have raisedQ0 : Derives Δ (formulaValue (template R) w.castSucc z.castSucc f.castSucc (V 0)) := of_eq (formulaValue_rename (template R) w z f (v 0) Fin.castSucc) (under q0 E)
  have raisedQ1 : Derives Δ (formulaValue (reflexive R) w.castSucc z.castSucc f.castSucc (V 1)) := of_eq (formulaValue_rename (reflexive R) w z f (v 1) Fin.castSucc) (under q1 E)
  have raisedQ2 : Derives Δ (formulaValue (transitive R) w.castSucc z.castSucc f.castSucc (V 2)) := of_eq (formulaValue_rename (transitive R) w z f (v 2) Fin.castSucc) (under q2 E)
  have raisedQ3 : Derives Δ (formulaValue (body1 R) w.castSucc A1.castSucc f.castSucc (V 3)) := of_eq (formulaValue_rename (body1 R) w A1 f (v 3) Fin.castSucc) (under q3 E)
  have raisedQ4 : Derives Δ (formulaValue (body2 R) w.castSucc A2.castSucc f.castSucc (V 4)) := of_eq (formulaValue_rename (body2 R) w A2 f (v 4) Fin.castSucc) (under q4 E)
  have raisedQ5 : Derives Δ (formulaValue (tails R 0) w.castSucc A3.castSucc f.castSucc (V 5)) := of_eq (formulaValue_rename (tails R 0) w A3 f (v 5) Fin.castSucc) (under q5 E)
  have raisedQ6 : Derives Δ (formulaValue (tails R 1) w.castSucc A3.castSucc f.castSucc (V 6)) := of_eq (formulaValue_rename (tails R 1) w A3 f (v 6) Fin.castSucc) (under q6 E)
  have raisedQ7 : Derives Δ (formulaValue (tails R 2) w.castSucc A3.castSucc f.castSucc (V 7)) := of_eq (formulaValue_rename (tails R 2) w A3 f (v 7) Fin.castSucc) (under q7 E)
  have raisedQ8 : Derives Δ (formulaValue (tails R 3) w.castSucc A3.castSucc f.castSucc (V 8)) := of_eq (formulaValue_rename (tails R 3) w A3 f (v 8) Fin.castSucc) (under q8 E)
  have raisedQ9 : Derives Δ (formulaValue (tails R 4) w.castSucc A3.castSucc f.castSucc (V 9)) := of_eq (formulaValue_rename (tails R 4) w A3 f (v 9) Fin.castSucc) (under q9 E)
  have raisedQ10 : Derives Δ (formulaValue (atoms R 0) w.castSucc A3.castSucc f.castSucc (V 10)) := of_eq (formulaValue_rename (atoms R 0) w A3 f (v 10) Fin.castSucc) (under q10 E)
  have raisedQ11 : Derives Δ (formulaValue (atoms R 1) w.castSucc A3.castSucc f.castSucc (V 11)) := of_eq (formulaValue_rename (atoms R 1) w A3 f (v 11) Fin.castSucc) (under q11 E)
  have hout := produce_13 (ZFContext.under hZ E) R w.castSucc z.castSucc A1.castSucc A2.castSucc A3.castSucc f.castSucc V hw1 h01 h11 h21 h31 hf1
    raisedQ0
    raisedQ1
    raisedQ2
    raisedQ3
    raisedQ4
    raisedQ5
    raisedQ6
    raisedQ7
    raisedQ8
    raisedQ9
    raisedQ10
    raisedQ11
    hE
  exact of_eq (rawExists_rename R w z A1 A2 A3 f Fin.castSucc).symm hout

private theorem produce_11 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w z A1 A2 A3 f : Fin m) (v : Fin 16 → Fin m) (hw : Derives Γ (omega w))
    (h0 : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (h3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (q0 : Derives Γ (formulaValue (template R) w z f (v 0)))
    (q1 : Derives Γ (formulaValue (reflexive R) w z f (v 1)))
    (q2 : Derives Γ (formulaValue (transitive R) w z f (v 2)))
    (q3 : Derives Γ (formulaValue (body1 R) w A1 f (v 3)))
    (q4 : Derives Γ (formulaValue (body2 R) w A2 f (v 4)))
    (q5 : Derives Γ (formulaValue (tails R 0) w A3 f (v 5)))
    (q6 : Derives Γ (formulaValue (tails R 1) w A3 f (v 6)))
    (q7 : Derives Γ (formulaValue (tails R 2) w A3 f (v 7)))
    (q8 : Derives Γ (formulaValue (tails R 3) w A3 f (v 8)))
    (q9 : Derives Γ (formulaValue (tails R 4) w A3 f (v 9)))
    (q10 : Derives Γ (formulaValue (atoms R 0) w A3 f (v 10)))
    : Derives Γ (rawExists R w z A1 A2 A3 f) := by
  have hFree : Derives Γ (SyntaxNumeralSyntax.numeral (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length f) :=
    of_eq (congrArg (fun t => SyntaxNumeralSyntax.numeral t f) (show (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length = n+2 from List.length_replicate).symm) hf
  let E := formulaValue (atoms R 1) w.castSucc A3.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (PureQuotationTypedFormulas.exists_typed hZ (atoms R 1) w A3 f hw h3 hFree)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  let V : Fin 16 → Fin (m+1) := fun j => if j = 11 then Fin.last m else (v j).castSucc
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have h01 := of_eq (SyntaxNumeralSyntax.numeral_rename 0 z Fin.castSucc) (under h0 E)
  have h11 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 A1 Fin.castSucc) (under h1 E)
  have h21 := of_eq (SyntaxNumeralSyntax.numeral_rename 2 A2 Fin.castSucc) (under h2 E)
  have h31 := of_eq (SyntaxNumeralSyntax.numeral_rename 3 A3 Fin.castSucc) (under h3 E)
  have hf1 := of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f Fin.castSucc) (under hf E)
  have raisedQ0 : Derives Δ (formulaValue (template R) w.castSucc z.castSucc f.castSucc (V 0)) := of_eq (formulaValue_rename (template R) w z f (v 0) Fin.castSucc) (under q0 E)
  have raisedQ1 : Derives Δ (formulaValue (reflexive R) w.castSucc z.castSucc f.castSucc (V 1)) := of_eq (formulaValue_rename (reflexive R) w z f (v 1) Fin.castSucc) (under q1 E)
  have raisedQ2 : Derives Δ (formulaValue (transitive R) w.castSucc z.castSucc f.castSucc (V 2)) := of_eq (formulaValue_rename (transitive R) w z f (v 2) Fin.castSucc) (under q2 E)
  have raisedQ3 : Derives Δ (formulaValue (body1 R) w.castSucc A1.castSucc f.castSucc (V 3)) := of_eq (formulaValue_rename (body1 R) w A1 f (v 3) Fin.castSucc) (under q3 E)
  have raisedQ4 : Derives Δ (formulaValue (body2 R) w.castSucc A2.castSucc f.castSucc (V 4)) := of_eq (formulaValue_rename (body2 R) w A2 f (v 4) Fin.castSucc) (under q4 E)
  have raisedQ5 : Derives Δ (formulaValue (tails R 0) w.castSucc A3.castSucc f.castSucc (V 5)) := of_eq (formulaValue_rename (tails R 0) w A3 f (v 5) Fin.castSucc) (under q5 E)
  have raisedQ6 : Derives Δ (formulaValue (tails R 1) w.castSucc A3.castSucc f.castSucc (V 6)) := of_eq (formulaValue_rename (tails R 1) w A3 f (v 6) Fin.castSucc) (under q6 E)
  have raisedQ7 : Derives Δ (formulaValue (tails R 2) w.castSucc A3.castSucc f.castSucc (V 7)) := of_eq (formulaValue_rename (tails R 2) w A3 f (v 7) Fin.castSucc) (under q7 E)
  have raisedQ8 : Derives Δ (formulaValue (tails R 3) w.castSucc A3.castSucc f.castSucc (V 8)) := of_eq (formulaValue_rename (tails R 3) w A3 f (v 8) Fin.castSucc) (under q8 E)
  have raisedQ9 : Derives Δ (formulaValue (tails R 4) w.castSucc A3.castSucc f.castSucc (V 9)) := of_eq (formulaValue_rename (tails R 4) w A3 f (v 9) Fin.castSucc) (under q9 E)
  have raisedQ10 : Derives Δ (formulaValue (atoms R 0) w.castSucc A3.castSucc f.castSucc (V 10)) := of_eq (formulaValue_rename (atoms R 0) w A3 f (v 10) Fin.castSucc) (under q10 E)
  have hout := produce_12 (ZFContext.under hZ E) R w.castSucc z.castSucc A1.castSucc A2.castSucc A3.castSucc f.castSucc V hw1 h01 h11 h21 h31 hf1
    raisedQ0
    raisedQ1
    raisedQ2
    raisedQ3
    raisedQ4
    raisedQ5
    raisedQ6
    raisedQ7
    raisedQ8
    raisedQ9
    raisedQ10
    hE
  exact of_eq (rawExists_rename R w z A1 A2 A3 f Fin.castSucc).symm hout

private theorem produce_10 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w z A1 A2 A3 f : Fin m) (v : Fin 16 → Fin m) (hw : Derives Γ (omega w))
    (h0 : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (h3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (q0 : Derives Γ (formulaValue (template R) w z f (v 0)))
    (q1 : Derives Γ (formulaValue (reflexive R) w z f (v 1)))
    (q2 : Derives Γ (formulaValue (transitive R) w z f (v 2)))
    (q3 : Derives Γ (formulaValue (body1 R) w A1 f (v 3)))
    (q4 : Derives Γ (formulaValue (body2 R) w A2 f (v 4)))
    (q5 : Derives Γ (formulaValue (tails R 0) w A3 f (v 5)))
    (q6 : Derives Γ (formulaValue (tails R 1) w A3 f (v 6)))
    (q7 : Derives Γ (formulaValue (tails R 2) w A3 f (v 7)))
    (q8 : Derives Γ (formulaValue (tails R 3) w A3 f (v 8)))
    (q9 : Derives Γ (formulaValue (tails R 4) w A3 f (v 9)))
    : Derives Γ (rawExists R w z A1 A2 A3 f) := by
  have hFree : Derives Γ (SyntaxNumeralSyntax.numeral (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length f) :=
    of_eq (congrArg (fun t => SyntaxNumeralSyntax.numeral t f) (show (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length = n+2 from List.length_replicate).symm) hf
  let E := formulaValue (atoms R 0) w.castSucc A3.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (PureQuotationTypedFormulas.exists_typed hZ (atoms R 0) w A3 f hw h3 hFree)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  let V : Fin 16 → Fin (m+1) := fun j => if j = 10 then Fin.last m else (v j).castSucc
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have h01 := of_eq (SyntaxNumeralSyntax.numeral_rename 0 z Fin.castSucc) (under h0 E)
  have h11 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 A1 Fin.castSucc) (under h1 E)
  have h21 := of_eq (SyntaxNumeralSyntax.numeral_rename 2 A2 Fin.castSucc) (under h2 E)
  have h31 := of_eq (SyntaxNumeralSyntax.numeral_rename 3 A3 Fin.castSucc) (under h3 E)
  have hf1 := of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f Fin.castSucc) (under hf E)
  have raisedQ0 : Derives Δ (formulaValue (template R) w.castSucc z.castSucc f.castSucc (V 0)) := of_eq (formulaValue_rename (template R) w z f (v 0) Fin.castSucc) (under q0 E)
  have raisedQ1 : Derives Δ (formulaValue (reflexive R) w.castSucc z.castSucc f.castSucc (V 1)) := of_eq (formulaValue_rename (reflexive R) w z f (v 1) Fin.castSucc) (under q1 E)
  have raisedQ2 : Derives Δ (formulaValue (transitive R) w.castSucc z.castSucc f.castSucc (V 2)) := of_eq (formulaValue_rename (transitive R) w z f (v 2) Fin.castSucc) (under q2 E)
  have raisedQ3 : Derives Δ (formulaValue (body1 R) w.castSucc A1.castSucc f.castSucc (V 3)) := of_eq (formulaValue_rename (body1 R) w A1 f (v 3) Fin.castSucc) (under q3 E)
  have raisedQ4 : Derives Δ (formulaValue (body2 R) w.castSucc A2.castSucc f.castSucc (V 4)) := of_eq (formulaValue_rename (body2 R) w A2 f (v 4) Fin.castSucc) (under q4 E)
  have raisedQ5 : Derives Δ (formulaValue (tails R 0) w.castSucc A3.castSucc f.castSucc (V 5)) := of_eq (formulaValue_rename (tails R 0) w A3 f (v 5) Fin.castSucc) (under q5 E)
  have raisedQ6 : Derives Δ (formulaValue (tails R 1) w.castSucc A3.castSucc f.castSucc (V 6)) := of_eq (formulaValue_rename (tails R 1) w A3 f (v 6) Fin.castSucc) (under q6 E)
  have raisedQ7 : Derives Δ (formulaValue (tails R 2) w.castSucc A3.castSucc f.castSucc (V 7)) := of_eq (formulaValue_rename (tails R 2) w A3 f (v 7) Fin.castSucc) (under q7 E)
  have raisedQ8 : Derives Δ (formulaValue (tails R 3) w.castSucc A3.castSucc f.castSucc (V 8)) := of_eq (formulaValue_rename (tails R 3) w A3 f (v 8) Fin.castSucc) (under q8 E)
  have raisedQ9 : Derives Δ (formulaValue (tails R 4) w.castSucc A3.castSucc f.castSucc (V 9)) := of_eq (formulaValue_rename (tails R 4) w A3 f (v 9) Fin.castSucc) (under q9 E)
  have hout := produce_11 (ZFContext.under hZ E) R w.castSucc z.castSucc A1.castSucc A2.castSucc A3.castSucc f.castSucc V hw1 h01 h11 h21 h31 hf1
    raisedQ0
    raisedQ1
    raisedQ2
    raisedQ3
    raisedQ4
    raisedQ5
    raisedQ6
    raisedQ7
    raisedQ8
    raisedQ9
    hE
  exact of_eq (rawExists_rename R w z A1 A2 A3 f Fin.castSucc).symm hout

private theorem produce_9 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w z A1 A2 A3 f : Fin m) (v : Fin 16 → Fin m) (hw : Derives Γ (omega w))
    (h0 : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (h3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (q0 : Derives Γ (formulaValue (template R) w z f (v 0)))
    (q1 : Derives Γ (formulaValue (reflexive R) w z f (v 1)))
    (q2 : Derives Γ (formulaValue (transitive R) w z f (v 2)))
    (q3 : Derives Γ (formulaValue (body1 R) w A1 f (v 3)))
    (q4 : Derives Γ (formulaValue (body2 R) w A2 f (v 4)))
    (q5 : Derives Γ (formulaValue (tails R 0) w A3 f (v 5)))
    (q6 : Derives Γ (formulaValue (tails R 1) w A3 f (v 6)))
    (q7 : Derives Γ (formulaValue (tails R 2) w A3 f (v 7)))
    (q8 : Derives Γ (formulaValue (tails R 3) w A3 f (v 8)))
    : Derives Γ (rawExists R w z A1 A2 A3 f) := by
  have hFree : Derives Γ (SyntaxNumeralSyntax.numeral (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length f) :=
    of_eq (congrArg (fun t => SyntaxNumeralSyntax.numeral t f) (show (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length = n+2 from List.length_replicate).symm) hf
  let E := formulaValue (tails R 4) w.castSucc A3.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (PureQuotationTypedFormulas.exists_typed hZ (tails R 4) w A3 f hw h3 hFree)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  let V : Fin 16 → Fin (m+1) := fun j => if j = 9 then Fin.last m else (v j).castSucc
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have h01 := of_eq (SyntaxNumeralSyntax.numeral_rename 0 z Fin.castSucc) (under h0 E)
  have h11 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 A1 Fin.castSucc) (under h1 E)
  have h21 := of_eq (SyntaxNumeralSyntax.numeral_rename 2 A2 Fin.castSucc) (under h2 E)
  have h31 := of_eq (SyntaxNumeralSyntax.numeral_rename 3 A3 Fin.castSucc) (under h3 E)
  have hf1 := of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f Fin.castSucc) (under hf E)
  have raisedQ0 : Derives Δ (formulaValue (template R) w.castSucc z.castSucc f.castSucc (V 0)) := of_eq (formulaValue_rename (template R) w z f (v 0) Fin.castSucc) (under q0 E)
  have raisedQ1 : Derives Δ (formulaValue (reflexive R) w.castSucc z.castSucc f.castSucc (V 1)) := of_eq (formulaValue_rename (reflexive R) w z f (v 1) Fin.castSucc) (under q1 E)
  have raisedQ2 : Derives Δ (formulaValue (transitive R) w.castSucc z.castSucc f.castSucc (V 2)) := of_eq (formulaValue_rename (transitive R) w z f (v 2) Fin.castSucc) (under q2 E)
  have raisedQ3 : Derives Δ (formulaValue (body1 R) w.castSucc A1.castSucc f.castSucc (V 3)) := of_eq (formulaValue_rename (body1 R) w A1 f (v 3) Fin.castSucc) (under q3 E)
  have raisedQ4 : Derives Δ (formulaValue (body2 R) w.castSucc A2.castSucc f.castSucc (V 4)) := of_eq (formulaValue_rename (body2 R) w A2 f (v 4) Fin.castSucc) (under q4 E)
  have raisedQ5 : Derives Δ (formulaValue (tails R 0) w.castSucc A3.castSucc f.castSucc (V 5)) := of_eq (formulaValue_rename (tails R 0) w A3 f (v 5) Fin.castSucc) (under q5 E)
  have raisedQ6 : Derives Δ (formulaValue (tails R 1) w.castSucc A3.castSucc f.castSucc (V 6)) := of_eq (formulaValue_rename (tails R 1) w A3 f (v 6) Fin.castSucc) (under q6 E)
  have raisedQ7 : Derives Δ (formulaValue (tails R 2) w.castSucc A3.castSucc f.castSucc (V 7)) := of_eq (formulaValue_rename (tails R 2) w A3 f (v 7) Fin.castSucc) (under q7 E)
  have raisedQ8 : Derives Δ (formulaValue (tails R 3) w.castSucc A3.castSucc f.castSucc (V 8)) := of_eq (formulaValue_rename (tails R 3) w A3 f (v 8) Fin.castSucc) (under q8 E)
  have hout := produce_10 (ZFContext.under hZ E) R w.castSucc z.castSucc A1.castSucc A2.castSucc A3.castSucc f.castSucc V hw1 h01 h11 h21 h31 hf1
    raisedQ0
    raisedQ1
    raisedQ2
    raisedQ3
    raisedQ4
    raisedQ5
    raisedQ6
    raisedQ7
    raisedQ8
    hE
  exact of_eq (rawExists_rename R w z A1 A2 A3 f Fin.castSucc).symm hout

private theorem produce_8 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w z A1 A2 A3 f : Fin m) (v : Fin 16 → Fin m) (hw : Derives Γ (omega w))
    (h0 : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (h3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (q0 : Derives Γ (formulaValue (template R) w z f (v 0)))
    (q1 : Derives Γ (formulaValue (reflexive R) w z f (v 1)))
    (q2 : Derives Γ (formulaValue (transitive R) w z f (v 2)))
    (q3 : Derives Γ (formulaValue (body1 R) w A1 f (v 3)))
    (q4 : Derives Γ (formulaValue (body2 R) w A2 f (v 4)))
    (q5 : Derives Γ (formulaValue (tails R 0) w A3 f (v 5)))
    (q6 : Derives Γ (formulaValue (tails R 1) w A3 f (v 6)))
    (q7 : Derives Γ (formulaValue (tails R 2) w A3 f (v 7)))
    : Derives Γ (rawExists R w z A1 A2 A3 f) := by
  have hFree : Derives Γ (SyntaxNumeralSyntax.numeral (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length f) :=
    of_eq (congrArg (fun t => SyntaxNumeralSyntax.numeral t f) (show (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length = n+2 from List.length_replicate).symm) hf
  let E := formulaValue (tails R 3) w.castSucc A3.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (PureQuotationTypedFormulas.exists_typed hZ (tails R 3) w A3 f hw h3 hFree)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  let V : Fin 16 → Fin (m+1) := fun j => if j = 8 then Fin.last m else (v j).castSucc
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have h01 := of_eq (SyntaxNumeralSyntax.numeral_rename 0 z Fin.castSucc) (under h0 E)
  have h11 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 A1 Fin.castSucc) (under h1 E)
  have h21 := of_eq (SyntaxNumeralSyntax.numeral_rename 2 A2 Fin.castSucc) (under h2 E)
  have h31 := of_eq (SyntaxNumeralSyntax.numeral_rename 3 A3 Fin.castSucc) (under h3 E)
  have hf1 := of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f Fin.castSucc) (under hf E)
  have raisedQ0 : Derives Δ (formulaValue (template R) w.castSucc z.castSucc f.castSucc (V 0)) := of_eq (formulaValue_rename (template R) w z f (v 0) Fin.castSucc) (under q0 E)
  have raisedQ1 : Derives Δ (formulaValue (reflexive R) w.castSucc z.castSucc f.castSucc (V 1)) := of_eq (formulaValue_rename (reflexive R) w z f (v 1) Fin.castSucc) (under q1 E)
  have raisedQ2 : Derives Δ (formulaValue (transitive R) w.castSucc z.castSucc f.castSucc (V 2)) := of_eq (formulaValue_rename (transitive R) w z f (v 2) Fin.castSucc) (under q2 E)
  have raisedQ3 : Derives Δ (formulaValue (body1 R) w.castSucc A1.castSucc f.castSucc (V 3)) := of_eq (formulaValue_rename (body1 R) w A1 f (v 3) Fin.castSucc) (under q3 E)
  have raisedQ4 : Derives Δ (formulaValue (body2 R) w.castSucc A2.castSucc f.castSucc (V 4)) := of_eq (formulaValue_rename (body2 R) w A2 f (v 4) Fin.castSucc) (under q4 E)
  have raisedQ5 : Derives Δ (formulaValue (tails R 0) w.castSucc A3.castSucc f.castSucc (V 5)) := of_eq (formulaValue_rename (tails R 0) w A3 f (v 5) Fin.castSucc) (under q5 E)
  have raisedQ6 : Derives Δ (formulaValue (tails R 1) w.castSucc A3.castSucc f.castSucc (V 6)) := of_eq (formulaValue_rename (tails R 1) w A3 f (v 6) Fin.castSucc) (under q6 E)
  have raisedQ7 : Derives Δ (formulaValue (tails R 2) w.castSucc A3.castSucc f.castSucc (V 7)) := of_eq (formulaValue_rename (tails R 2) w A3 f (v 7) Fin.castSucc) (under q7 E)
  have hout := produce_9 (ZFContext.under hZ E) R w.castSucc z.castSucc A1.castSucc A2.castSucc A3.castSucc f.castSucc V hw1 h01 h11 h21 h31 hf1
    raisedQ0
    raisedQ1
    raisedQ2
    raisedQ3
    raisedQ4
    raisedQ5
    raisedQ6
    raisedQ7
    hE
  exact of_eq (rawExists_rename R w z A1 A2 A3 f Fin.castSucc).symm hout

private theorem produce_7 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w z A1 A2 A3 f : Fin m) (v : Fin 16 → Fin m) (hw : Derives Γ (omega w))
    (h0 : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (h3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (q0 : Derives Γ (formulaValue (template R) w z f (v 0)))
    (q1 : Derives Γ (formulaValue (reflexive R) w z f (v 1)))
    (q2 : Derives Γ (formulaValue (transitive R) w z f (v 2)))
    (q3 : Derives Γ (formulaValue (body1 R) w A1 f (v 3)))
    (q4 : Derives Γ (formulaValue (body2 R) w A2 f (v 4)))
    (q5 : Derives Γ (formulaValue (tails R 0) w A3 f (v 5)))
    (q6 : Derives Γ (formulaValue (tails R 1) w A3 f (v 6)))
    : Derives Γ (rawExists R w z A1 A2 A3 f) := by
  have hFree : Derives Γ (SyntaxNumeralSyntax.numeral (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length f) :=
    of_eq (congrArg (fun t => SyntaxNumeralSyntax.numeral t f) (show (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length = n+2 from List.length_replicate).symm) hf
  let E := formulaValue (tails R 2) w.castSucc A3.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (PureQuotationTypedFormulas.exists_typed hZ (tails R 2) w A3 f hw h3 hFree)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  let V : Fin 16 → Fin (m+1) := fun j => if j = 7 then Fin.last m else (v j).castSucc
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have h01 := of_eq (SyntaxNumeralSyntax.numeral_rename 0 z Fin.castSucc) (under h0 E)
  have h11 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 A1 Fin.castSucc) (under h1 E)
  have h21 := of_eq (SyntaxNumeralSyntax.numeral_rename 2 A2 Fin.castSucc) (under h2 E)
  have h31 := of_eq (SyntaxNumeralSyntax.numeral_rename 3 A3 Fin.castSucc) (under h3 E)
  have hf1 := of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f Fin.castSucc) (under hf E)
  have raisedQ0 : Derives Δ (formulaValue (template R) w.castSucc z.castSucc f.castSucc (V 0)) := of_eq (formulaValue_rename (template R) w z f (v 0) Fin.castSucc) (under q0 E)
  have raisedQ1 : Derives Δ (formulaValue (reflexive R) w.castSucc z.castSucc f.castSucc (V 1)) := of_eq (formulaValue_rename (reflexive R) w z f (v 1) Fin.castSucc) (under q1 E)
  have raisedQ2 : Derives Δ (formulaValue (transitive R) w.castSucc z.castSucc f.castSucc (V 2)) := of_eq (formulaValue_rename (transitive R) w z f (v 2) Fin.castSucc) (under q2 E)
  have raisedQ3 : Derives Δ (formulaValue (body1 R) w.castSucc A1.castSucc f.castSucc (V 3)) := of_eq (formulaValue_rename (body1 R) w A1 f (v 3) Fin.castSucc) (under q3 E)
  have raisedQ4 : Derives Δ (formulaValue (body2 R) w.castSucc A2.castSucc f.castSucc (V 4)) := of_eq (formulaValue_rename (body2 R) w A2 f (v 4) Fin.castSucc) (under q4 E)
  have raisedQ5 : Derives Δ (formulaValue (tails R 0) w.castSucc A3.castSucc f.castSucc (V 5)) := of_eq (formulaValue_rename (tails R 0) w A3 f (v 5) Fin.castSucc) (under q5 E)
  have raisedQ6 : Derives Δ (formulaValue (tails R 1) w.castSucc A3.castSucc f.castSucc (V 6)) := of_eq (formulaValue_rename (tails R 1) w A3 f (v 6) Fin.castSucc) (under q6 E)
  have hout := produce_8 (ZFContext.under hZ E) R w.castSucc z.castSucc A1.castSucc A2.castSucc A3.castSucc f.castSucc V hw1 h01 h11 h21 h31 hf1
    raisedQ0
    raisedQ1
    raisedQ2
    raisedQ3
    raisedQ4
    raisedQ5
    raisedQ6
    hE
  exact of_eq (rawExists_rename R w z A1 A2 A3 f Fin.castSucc).symm hout

private theorem produce_6 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w z A1 A2 A3 f : Fin m) (v : Fin 16 → Fin m) (hw : Derives Γ (omega w))
    (h0 : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (h3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (q0 : Derives Γ (formulaValue (template R) w z f (v 0)))
    (q1 : Derives Γ (formulaValue (reflexive R) w z f (v 1)))
    (q2 : Derives Γ (formulaValue (transitive R) w z f (v 2)))
    (q3 : Derives Γ (formulaValue (body1 R) w A1 f (v 3)))
    (q4 : Derives Γ (formulaValue (body2 R) w A2 f (v 4)))
    (q5 : Derives Γ (formulaValue (tails R 0) w A3 f (v 5)))
    : Derives Γ (rawExists R w z A1 A2 A3 f) := by
  have hFree : Derives Γ (SyntaxNumeralSyntax.numeral (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length f) :=
    of_eq (congrArg (fun t => SyntaxNumeralSyntax.numeral t f) (show (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length = n+2 from List.length_replicate).symm) hf
  let E := formulaValue (tails R 1) w.castSucc A3.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (PureQuotationTypedFormulas.exists_typed hZ (tails R 1) w A3 f hw h3 hFree)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  let V : Fin 16 → Fin (m+1) := fun j => if j = 6 then Fin.last m else (v j).castSucc
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have h01 := of_eq (SyntaxNumeralSyntax.numeral_rename 0 z Fin.castSucc) (under h0 E)
  have h11 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 A1 Fin.castSucc) (under h1 E)
  have h21 := of_eq (SyntaxNumeralSyntax.numeral_rename 2 A2 Fin.castSucc) (under h2 E)
  have h31 := of_eq (SyntaxNumeralSyntax.numeral_rename 3 A3 Fin.castSucc) (under h3 E)
  have hf1 := of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f Fin.castSucc) (under hf E)
  have raisedQ0 : Derives Δ (formulaValue (template R) w.castSucc z.castSucc f.castSucc (V 0)) := of_eq (formulaValue_rename (template R) w z f (v 0) Fin.castSucc) (under q0 E)
  have raisedQ1 : Derives Δ (formulaValue (reflexive R) w.castSucc z.castSucc f.castSucc (V 1)) := of_eq (formulaValue_rename (reflexive R) w z f (v 1) Fin.castSucc) (under q1 E)
  have raisedQ2 : Derives Δ (formulaValue (transitive R) w.castSucc z.castSucc f.castSucc (V 2)) := of_eq (formulaValue_rename (transitive R) w z f (v 2) Fin.castSucc) (under q2 E)
  have raisedQ3 : Derives Δ (formulaValue (body1 R) w.castSucc A1.castSucc f.castSucc (V 3)) := of_eq (formulaValue_rename (body1 R) w A1 f (v 3) Fin.castSucc) (under q3 E)
  have raisedQ4 : Derives Δ (formulaValue (body2 R) w.castSucc A2.castSucc f.castSucc (V 4)) := of_eq (formulaValue_rename (body2 R) w A2 f (v 4) Fin.castSucc) (under q4 E)
  have raisedQ5 : Derives Δ (formulaValue (tails R 0) w.castSucc A3.castSucc f.castSucc (V 5)) := of_eq (formulaValue_rename (tails R 0) w A3 f (v 5) Fin.castSucc) (under q5 E)
  have hout := produce_7 (ZFContext.under hZ E) R w.castSucc z.castSucc A1.castSucc A2.castSucc A3.castSucc f.castSucc V hw1 h01 h11 h21 h31 hf1
    raisedQ0
    raisedQ1
    raisedQ2
    raisedQ3
    raisedQ4
    raisedQ5
    hE
  exact of_eq (rawExists_rename R w z A1 A2 A3 f Fin.castSucc).symm hout

private theorem produce_5 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w z A1 A2 A3 f : Fin m) (v : Fin 16 → Fin m) (hw : Derives Γ (omega w))
    (h0 : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (h3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (q0 : Derives Γ (formulaValue (template R) w z f (v 0)))
    (q1 : Derives Γ (formulaValue (reflexive R) w z f (v 1)))
    (q2 : Derives Γ (formulaValue (transitive R) w z f (v 2)))
    (q3 : Derives Γ (formulaValue (body1 R) w A1 f (v 3)))
    (q4 : Derives Γ (formulaValue (body2 R) w A2 f (v 4)))
    : Derives Γ (rawExists R w z A1 A2 A3 f) := by
  have hFree : Derives Γ (SyntaxNumeralSyntax.numeral (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length f) :=
    of_eq (congrArg (fun t => SyntaxNumeralSyntax.numeral t f) (show (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length = n+2 from List.length_replicate).symm) hf
  let E := formulaValue (tails R 0) w.castSucc A3.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (PureQuotationTypedFormulas.exists_typed hZ (tails R 0) w A3 f hw h3 hFree)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  let V : Fin 16 → Fin (m+1) := fun j => if j = 5 then Fin.last m else (v j).castSucc
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have h01 := of_eq (SyntaxNumeralSyntax.numeral_rename 0 z Fin.castSucc) (under h0 E)
  have h11 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 A1 Fin.castSucc) (under h1 E)
  have h21 := of_eq (SyntaxNumeralSyntax.numeral_rename 2 A2 Fin.castSucc) (under h2 E)
  have h31 := of_eq (SyntaxNumeralSyntax.numeral_rename 3 A3 Fin.castSucc) (under h3 E)
  have hf1 := of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f Fin.castSucc) (under hf E)
  have raisedQ0 : Derives Δ (formulaValue (template R) w.castSucc z.castSucc f.castSucc (V 0)) := of_eq (formulaValue_rename (template R) w z f (v 0) Fin.castSucc) (under q0 E)
  have raisedQ1 : Derives Δ (formulaValue (reflexive R) w.castSucc z.castSucc f.castSucc (V 1)) := of_eq (formulaValue_rename (reflexive R) w z f (v 1) Fin.castSucc) (under q1 E)
  have raisedQ2 : Derives Δ (formulaValue (transitive R) w.castSucc z.castSucc f.castSucc (V 2)) := of_eq (formulaValue_rename (transitive R) w z f (v 2) Fin.castSucc) (under q2 E)
  have raisedQ3 : Derives Δ (formulaValue (body1 R) w.castSucc A1.castSucc f.castSucc (V 3)) := of_eq (formulaValue_rename (body1 R) w A1 f (v 3) Fin.castSucc) (under q3 E)
  have raisedQ4 : Derives Δ (formulaValue (body2 R) w.castSucc A2.castSucc f.castSucc (V 4)) := of_eq (formulaValue_rename (body2 R) w A2 f (v 4) Fin.castSucc) (under q4 E)
  have hout := produce_6 (ZFContext.under hZ E) R w.castSucc z.castSucc A1.castSucc A2.castSucc A3.castSucc f.castSucc V hw1 h01 h11 h21 h31 hf1
    raisedQ0
    raisedQ1
    raisedQ2
    raisedQ3
    raisedQ4
    hE
  exact of_eq (rawExists_rename R w z A1 A2 A3 f Fin.castSucc).symm hout

private theorem produce_4 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w z A1 A2 A3 f : Fin m) (v : Fin 16 → Fin m) (hw : Derives Γ (omega w))
    (h0 : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (h3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (q0 : Derives Γ (formulaValue (template R) w z f (v 0)))
    (q1 : Derives Γ (formulaValue (reflexive R) w z f (v 1)))
    (q2 : Derives Γ (formulaValue (transitive R) w z f (v 2)))
    (q3 : Derives Γ (formulaValue (body1 R) w A1 f (v 3)))
    : Derives Γ (rawExists R w z A1 A2 A3 f) := by
  have hFree : Derives Γ (SyntaxNumeralSyntax.numeral (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length f) :=
    of_eq (congrArg (fun t => SyntaxNumeralSyntax.numeral t f) (show (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length = n+2 from List.length_replicate).symm) hf
  let E := formulaValue (body2 R) w.castSucc A2.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (PureQuotationTypedFormulas.exists_typed hZ (body2 R) w A2 f hw h2 hFree)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  let V : Fin 16 → Fin (m+1) := fun j => if j = 4 then Fin.last m else (v j).castSucc
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have h01 := of_eq (SyntaxNumeralSyntax.numeral_rename 0 z Fin.castSucc) (under h0 E)
  have h11 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 A1 Fin.castSucc) (under h1 E)
  have h21 := of_eq (SyntaxNumeralSyntax.numeral_rename 2 A2 Fin.castSucc) (under h2 E)
  have h31 := of_eq (SyntaxNumeralSyntax.numeral_rename 3 A3 Fin.castSucc) (under h3 E)
  have hf1 := of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f Fin.castSucc) (under hf E)
  have raisedQ0 : Derives Δ (formulaValue (template R) w.castSucc z.castSucc f.castSucc (V 0)) := of_eq (formulaValue_rename (template R) w z f (v 0) Fin.castSucc) (under q0 E)
  have raisedQ1 : Derives Δ (formulaValue (reflexive R) w.castSucc z.castSucc f.castSucc (V 1)) := of_eq (formulaValue_rename (reflexive R) w z f (v 1) Fin.castSucc) (under q1 E)
  have raisedQ2 : Derives Δ (formulaValue (transitive R) w.castSucc z.castSucc f.castSucc (V 2)) := of_eq (formulaValue_rename (transitive R) w z f (v 2) Fin.castSucc) (under q2 E)
  have raisedQ3 : Derives Δ (formulaValue (body1 R) w.castSucc A1.castSucc f.castSucc (V 3)) := of_eq (formulaValue_rename (body1 R) w A1 f (v 3) Fin.castSucc) (under q3 E)
  have hout := produce_5 (ZFContext.under hZ E) R w.castSucc z.castSucc A1.castSucc A2.castSucc A3.castSucc f.castSucc V hw1 h01 h11 h21 h31 hf1
    raisedQ0
    raisedQ1
    raisedQ2
    raisedQ3
    hE
  exact of_eq (rawExists_rename R w z A1 A2 A3 f Fin.castSucc).symm hout

private theorem produce_3 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w z A1 A2 A3 f : Fin m) (v : Fin 16 → Fin m) (hw : Derives Γ (omega w))
    (h0 : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (h3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (q0 : Derives Γ (formulaValue (template R) w z f (v 0)))
    (q1 : Derives Γ (formulaValue (reflexive R) w z f (v 1)))
    (q2 : Derives Γ (formulaValue (transitive R) w z f (v 2)))
    : Derives Γ (rawExists R w z A1 A2 A3 f) := by
  have hFree : Derives Γ (SyntaxNumeralSyntax.numeral (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length f) :=
    of_eq (congrArg (fun t => SyntaxNumeralSyntax.numeral t f) (show (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length = n+2 from List.length_replicate).symm) hf
  let E := formulaValue (body1 R) w.castSucc A1.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (PureQuotationTypedFormulas.exists_typed hZ (body1 R) w A1 f hw h1 hFree)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  let V : Fin 16 → Fin (m+1) := fun j => if j = 3 then Fin.last m else (v j).castSucc
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have h01 := of_eq (SyntaxNumeralSyntax.numeral_rename 0 z Fin.castSucc) (under h0 E)
  have h11 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 A1 Fin.castSucc) (under h1 E)
  have h21 := of_eq (SyntaxNumeralSyntax.numeral_rename 2 A2 Fin.castSucc) (under h2 E)
  have h31 := of_eq (SyntaxNumeralSyntax.numeral_rename 3 A3 Fin.castSucc) (under h3 E)
  have hf1 := of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f Fin.castSucc) (under hf E)
  have raisedQ0 : Derives Δ (formulaValue (template R) w.castSucc z.castSucc f.castSucc (V 0)) := of_eq (formulaValue_rename (template R) w z f (v 0) Fin.castSucc) (under q0 E)
  have raisedQ1 : Derives Δ (formulaValue (reflexive R) w.castSucc z.castSucc f.castSucc (V 1)) := of_eq (formulaValue_rename (reflexive R) w z f (v 1) Fin.castSucc) (under q1 E)
  have raisedQ2 : Derives Δ (formulaValue (transitive R) w.castSucc z.castSucc f.castSucc (V 2)) := of_eq (formulaValue_rename (transitive R) w z f (v 2) Fin.castSucc) (under q2 E)
  have hout := produce_4 (ZFContext.under hZ E) R w.castSucc z.castSucc A1.castSucc A2.castSucc A3.castSucc f.castSucc V hw1 h01 h11 h21 h31 hf1
    raisedQ0
    raisedQ1
    raisedQ2
    hE
  exact of_eq (rawExists_rename R w z A1 A2 A3 f Fin.castSucc).symm hout

private theorem produce_2 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w z A1 A2 A3 f : Fin m) (v : Fin 16 → Fin m) (hw : Derives Γ (omega w))
    (h0 : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (h3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (q0 : Derives Γ (formulaValue (template R) w z f (v 0)))
    (q1 : Derives Γ (formulaValue (reflexive R) w z f (v 1)))
    : Derives Γ (rawExists R w z A1 A2 A3 f) := by
  have hFree : Derives Γ (SyntaxNumeralSyntax.numeral (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length f) :=
    of_eq (congrArg (fun t => SyntaxNumeralSyntax.numeral t f) (show (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length = n+2 from List.length_replicate).symm) hf
  let E := formulaValue (transitive R) w.castSucc z.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (PureQuotationTypedFormulas.exists_typed hZ (transitive R) w z f hw h0 hFree)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  let V : Fin 16 → Fin (m+1) := fun j => if j = 2 then Fin.last m else (v j).castSucc
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have h01 := of_eq (SyntaxNumeralSyntax.numeral_rename 0 z Fin.castSucc) (under h0 E)
  have h11 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 A1 Fin.castSucc) (under h1 E)
  have h21 := of_eq (SyntaxNumeralSyntax.numeral_rename 2 A2 Fin.castSucc) (under h2 E)
  have h31 := of_eq (SyntaxNumeralSyntax.numeral_rename 3 A3 Fin.castSucc) (under h3 E)
  have hf1 := of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f Fin.castSucc) (under hf E)
  have raisedQ0 : Derives Δ (formulaValue (template R) w.castSucc z.castSucc f.castSucc (V 0)) := of_eq (formulaValue_rename (template R) w z f (v 0) Fin.castSucc) (under q0 E)
  have raisedQ1 : Derives Δ (formulaValue (reflexive R) w.castSucc z.castSucc f.castSucc (V 1)) := of_eq (formulaValue_rename (reflexive R) w z f (v 1) Fin.castSucc) (under q1 E)
  have hout := produce_3 (ZFContext.under hZ E) R w.castSucc z.castSucc A1.castSucc A2.castSucc A3.castSucc f.castSucc V hw1 h01 h11 h21 h31 hf1
    raisedQ0
    raisedQ1
    hE
  exact of_eq (rawExists_rename R w z A1 A2 A3 f Fin.castSucc).symm hout

private theorem produce_1 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w z A1 A2 A3 f : Fin m) (v : Fin 16 → Fin m) (hw : Derives Γ (omega w))
    (h0 : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (h3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (q0 : Derives Γ (formulaValue (template R) w z f (v 0)))
    : Derives Γ (rawExists R w z A1 A2 A3 f) := by
  have hFree : Derives Γ (SyntaxNumeralSyntax.numeral (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length f) :=
    of_eq (congrArg (fun t => SyntaxNumeralSyntax.numeral t f) (show (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length = n+2 from List.length_replicate).symm) hf
  let E := formulaValue (reflexive R) w.castSucc z.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (PureQuotationTypedFormulas.exists_typed hZ (reflexive R) w z f hw h0 hFree)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  let V : Fin 16 → Fin (m+1) := fun j => if j = 1 then Fin.last m else (v j).castSucc
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have h01 := of_eq (SyntaxNumeralSyntax.numeral_rename 0 z Fin.castSucc) (under h0 E)
  have h11 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 A1 Fin.castSucc) (under h1 E)
  have h21 := of_eq (SyntaxNumeralSyntax.numeral_rename 2 A2 Fin.castSucc) (under h2 E)
  have h31 := of_eq (SyntaxNumeralSyntax.numeral_rename 3 A3 Fin.castSucc) (under h3 E)
  have hf1 := of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f Fin.castSucc) (under hf E)
  have raisedQ0 : Derives Δ (formulaValue (template R) w.castSucc z.castSucc f.castSucc (V 0)) := of_eq (formulaValue_rename (template R) w z f (v 0) Fin.castSucc) (under q0 E)
  have hout := produce_2 (ZFContext.under hZ E) R w.castSucc z.castSucc A1.castSucc A2.castSucc A3.castSucc f.castSucc V hw1 h01 h11 h21 h31 hf1
    raisedQ0
    hE
  exact of_eq (rawExists_rename R w z A1 A2 A3 f Fin.castSucc).symm hout

private theorem produce_0 {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w z A1 A2 A3 f : Fin m) (v : Fin 16 → Fin m) (hw : Derives Γ (omega w))
    (h0 : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (h3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    : Derives Γ (rawExists R w z A1 A2 A3 f) := by
  have hFree : Derives Γ (SyntaxNumeralSyntax.numeral (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length f) :=
    of_eq (congrArg (fun t => SyntaxNumeralSyntax.numeral t f) (show (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (n+2)).length = n+2 from List.length_replicate).symm) hf
  let E := formulaValue (template R) w.castSucc z.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (PureQuotationTypedFormulas.exists_typed hZ (template R) w z f hw h0 hFree)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  let V : Fin 16 → Fin (m+1) := fun j => if j = 0 then Fin.last m else (v j).castSucc
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have h01 := of_eq (SyntaxNumeralSyntax.numeral_rename 0 z Fin.castSucc) (under h0 E)
  have h11 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 A1 Fin.castSucc) (under h1 E)
  have h21 := of_eq (SyntaxNumeralSyntax.numeral_rename 2 A2 Fin.castSucc) (under h2 E)
  have h31 := of_eq (SyntaxNumeralSyntax.numeral_rename 3 A3 Fin.castSucc) (under h3 E)
  have hf1 := of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) f Fin.castSucc) (under hf E)
  have hout := produce_1 (ZFContext.under hZ E) R w.castSucc z.castSucc A1.castSucc A2.castSucc A3.castSucc f.castSucc V hw1 h01 h11 h21 h31 hf1
    hE
  exact of_eq (rawExists_rename R w z A1 A2 A3 f Fin.castSucc).symm hout

/-- Actual raw quotation codes, types and all constructor fields are generated
inside original ZF. No quotation output, target code or proof oracle is an input.
The fixed source AST is later opened by the existing mixed-substitution engine;
this result does not restrict runtime target codes/scopes to external numerals. -/
theorem produce {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2))
    (w z A1 A2 A3 f : Fin m) (hw : Derives Γ (omega w))
    (h0 : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (h3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f)) : Derives Γ (rawExists R w z A1 A2 A3 f) :=
  produce_0 hZ R w z A1 A2 A3 f (fun _ => w) hw h0 h1 h2 h3 hf

def input {n m} (_R : Source.Formula (n+2)) (w z A1 A2 A3 f : Fin m) : Formula m :=
  (omega w).conj ((SyntaxNumeralSyntax.numeral 0 z).conj ((SyntaxNumeralSyntax.numeral 1 A1).conj ((SyntaxNumeralSyntax.numeral 2 A2).conj ((SyntaxNumeralSyntax.numeral 3 A3).conj ((SyntaxNumeralSyntax.numeral (n+2) f))))))

def sentence {n m} (R : Source.Formula (n+2)) (w z A1 A2 A3 f : Fin m) : Source.Sentence :=
  ((input R w z A1 A2 A3 f).imp (rawExists R w z A1 A2 A3 f)).close

theorem kernel_certificate {n m} (R : Source.Formula (n+2)) (w z A1 A2 A3 f : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence R w z A1 A2 A3 f)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input R w z A1 A2 A3 f
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact produce (ZFContext.add (ZFContext.source_ZF m) E) R w z A1 A2 A3 f
    (.conjL h)
    (.conjL (.conjR h))
    (.conjL (.conjR (.conjR h)))
    (.conjL (.conjR (.conjR (.conjR h))))
    (.conjL (.conjR (.conjR (.conjR (.conjR h)))))
    (.conjR (.conjR (.conjR (.conjR (.conjR h)))))

end PPAC.Migration.ForcingPreorderCode


namespace PPAC.Migration.ForcingPreorderCode
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open SetTheory.Definitional.Project (fo_bound_context fo_bound_variable)
attribute [local implicit_reducible] SetTheory.signature

private theorem native_source {k} (input : Source.Formula k) :
    native input = Syntax.formula (fun i => .fvar (fo_bound_variable i)) input := by
  unfold native
  rw [← Syntax.old_formula, Syntax.substitute]
  rfl

theorem template_as_source {n} (R : Source.Formula (n+2)) :
    template R = Syntax.formula (fun i => .fvar (fo_bound_variable i)) (source R) :=
  native_source (source R)

/-- The original first relation atom is literally R(r,q), with bound
indices r=2 and q=1; all original parameter slots are retained. -/
theorem atom_rq {n} (R : Source.Formula (n+2)) :
    atoms R 3 = Syntax.formula
      (Fin.lastCases (.bvar (.there .here))
        (Fin.lastCases (.bvar (.there (.there .here)))
          (fun i => .fvar (fo_bound_variable i.castSucc.castSucc)))) R := by
  simp only [atoms, t1, t2, t3, t4, matrix, body2, body1, transitive, template, native_source,
    source, ForcingAtomicBasic.preorder, Syntax.formula, andRight, allBody, impLeft, impRight,
    ReplacementPredicates.rel, Source.SetLanguage.relation, Syntax.rename]
  change Syntax.formula _ R = _
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Syntax.lift, Fin.lastCases_last, Fin.lastCases_castSucc, Term.weakenBound_bvar, Term.weakenBound_fvar]
  · refine Fin.lastCases ?_ (fun k => ?_) j <;> simp only [Syntax.lift, Fin.lastCases_last, Fin.lastCases_castSucc, Term.weakenBound_bvar, Term.weakenBound_fvar]

/-- The original second relation atom is literally R(q,p). -/
theorem atom_qp {n} (R : Source.Formula (n+2)) :
    atoms R 4 = Syntax.formula
      (Fin.lastCases (.bvar .here)
        (Fin.lastCases (.bvar (.there .here))
          (fun i => .fvar (fo_bound_variable i.castSucc.castSucc)))) R := by
  simp only [atoms, t1, t2, t3, t4, matrix, body2, body1, transitive, template, native_source,
    source, ForcingAtomicBasic.preorder, Syntax.formula, andRight, allBody, impLeft, impRight,
    ReplacementPredicates.rel, Source.SetLanguage.relation, Syntax.rename]
  change Syntax.formula _ R = _
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Syntax.lift, Fin.lastCases_last, Term.weakenBound_fvar]
  · refine Fin.lastCases ?_ (fun k => ?_) j <;> simp only [Syntax.lift, Fin.lastCases_last, Fin.lastCases_castSucc, Term.weakenBound_bvar, Term.weakenBound_fvar]

/-- The original concluding relation atom is literally R(r,p). -/
theorem atom_rp {n} (R : Source.Formula (n+2)) :
    atoms R 5 = Syntax.formula
      (Fin.lastCases (.bvar .here)
        (Fin.lastCases (.bvar (.there (.there .here)))
          (fun i => .fvar (fo_bound_variable i.castSucc.castSucc)))) R := by
  simp only [atoms, t1, t2, t3, t4, matrix, body2, body1, transitive, template, native_source,
    source, ForcingAtomicBasic.preorder, Syntax.formula, andRight, allBody, impLeft, impRight,
    ReplacementPredicates.rel, Source.SetLanguage.relation, Syntax.rename]
  change Syntax.formula _ R = _
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Syntax.lift, Fin.lastCases_last, Term.weakenBound_fvar]
  · refine Fin.lastCases ?_ (fun k => ?_) j <;> simp only [Syntax.lift, Fin.lastCases_last, Fin.lastCases_castSucc, Term.weakenBound_bvar, Term.weakenBound_fvar]

/-- Literal original member leaves, using the existing source/nativity bridge. -/
theorem atom_member_r {n} (R : Source.Formula (n+2)) :
    atoms R 0 = .rel .membership (.cons (.bvar (.there (.there .here)))
      (.cons (.fvar (fo_bound_variable (Fin.last n).castSucc)) .nil)) := by
  simp only [atoms, t1, t2, t3, t4, matrix, body2, body1, transitive, template, native_source,
    source, ForcingAtomicBasic.preorder, Syntax.formula, andRight, allBody, impLeft, impRight,
    Syntax.lift, Fin.lastCases_last, Fin.lastCases_castSucc, Term.weakenBound_bvar, Term.weakenBound_fvar] <;> rfl

theorem atom_member_q {n} (R : Source.Formula (n+2)) :
    atoms R 1 = .rel .membership (.cons (.bvar (.there .here))
      (.cons (.fvar (fo_bound_variable (Fin.last n).castSucc)) .nil)) := by
  simp only [atoms, t1, t2, t3, t4, matrix, body2, body1, transitive, template, native_source,
    source, ForcingAtomicBasic.preorder, Syntax.formula, andRight, allBody, impLeft, impRight,
    Syntax.lift, Fin.lastCases_last, Fin.lastCases_castSucc, Term.weakenBound_bvar, Term.weakenBound_fvar] <;> rfl

theorem atom_member_p {n} (R : Source.Formula (n+2)) :
    atoms R 2 = .rel .membership (.cons (.bvar .here)
      (.cons (.fvar (fo_bound_variable (Fin.last n).castSucc)) .nil)) := by
  simp only [atoms, t1, t2, t3, t4, matrix, body2, body1, transitive, template, native_source,
    source, ForcingAtomicBasic.preorder, Syntax.formula, andRight, allBody, impLeft, impRight,
    Syntax.lift, Fin.lastCases_last, Fin.lastCases_castSucc, Term.weakenBound_bvar, Term.weakenBound_fvar] <;> rfl


/-- The guard in the original reflexivity sentence is the literal member
formula with the bound condition at index zero and the original carrier slot. -/
theorem reflexive_member_tree {n} (R : Source.Formula (n+2)) :
    PureSyntaxQuotation.formulaTree (reflexiveLeaf R false) =
      YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree.node 2 ([PureSyntaxQuotation.Original.leaf 0,
        YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree.node 0 ([PureSyntaxQuotation.Original.leaf 0]),
        YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree.node 1 ([PureSyntaxQuotation.Original.leaf n])]) := by
  have hMember : reflexiveLeaf R false = .rel .membership (.cons (.bvar .here)
      (.cons (.fvar (fo_bound_variable (Fin.last n).castSucc)) .nil)) := by
    simp only [reflexiveLeaf, reflexiveBody, reflexive, template, native_source,
      source, ForcingAtomicBasic.preorder, Syntax.formula, andLeft, allBody, impLeft,
      Syntax.lift, Fin.lastCases_last, Fin.lastCases_castSucc, Term.weakenBound_bvar,
      Term.weakenBound_fvar] <;> rfl
  have hIndex : (fo_bound_variable (Fin.last n).castSucc).index = n :=
    ProjectNativeRenaming.variable_index (fun _ : Fin 1 => (Fin.last n).castSucc)
      (fo_bound_variable (0 : Fin 1))
  simp only [hMember, PureSyntaxQuotation.formulaTree, PureSyntaxQuotation.argumentTrees,
    PureSyntaxQuotation.termTree, hIndex]
  rfl

end PPAC.Migration.ForcingPreorderCode
