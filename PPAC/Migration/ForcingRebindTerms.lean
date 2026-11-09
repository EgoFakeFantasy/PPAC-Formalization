import PPAC.Migration.ForcingConditionRebind
import PPAC.Migration.ForcingOpenLift
import PPAC.Migration.Internal.AbstractTopVariablePoint
import PPAC.Migration.Internal.SyntaxCodedMixedTermFields

/-! Consume the ORIGINAL complete rebind compiler's SAME six witnesses.
The real bound/free tables yield the actual coded term-substitution equation;
no replacement table or term answer is supplied. This is the first operation
in full formula rebind/open/InstantiateTop cancellation, not that theorem. -/
namespace PPAC.Migration.ForcingRebindTerms
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open StructuralListFieldSyntax (field field_rename)
set_option maxRecDepth 16384
attribute [local irreducible] NaturalRecursionSyntax.matrix

def termValue {m} (bound : Bool) (w j head i I y : Fin m) : Formula m :=
  if bound then SyntaxVariableSyntax.code true w I y else ForcingConditionRebind.value w j head i y

theorem termValue_rename {m l} (bound : Bool) (w j head i I y : Fin m) (r : Fin m → Fin l) :
    (termValue bound w j head i I y).rename r = termValue bound (r w) (r j) (r head) (r i) (r I) (r y) := by
  cases bound <;> simp only [termValue, Bool.false_eq_true, ↓reduceIte, SyntaxVariableSyntax.code_rename, ForcingConditionRebind.value_rename]

def equation {m} (bound : Bool) (w a f A j x y i I : Fin m) (v : Fin 6 → Fin m) : Formula m :=
  (SyntaxCodedMixedTermSyntax.substituted w (v 3) (v 5) a f A f x y).iff (termValue bound w j (v 1) i I y)

theorem equation_rename {m l} (bound : Bool) (w a f A j x y i I : Fin m) (v : Fin 6 → Fin m) (r : Fin m → Fin l) :
    (equation bound w a f A j x y i I v).rename r = equation bound (r w) (r a) (r f) (r A) (r j) (r x) (r y) (r i) (r I) (fun k => r (v k)) := by
  simp only [equation, Formula.iff, Formula.rename, SyntaxCodedMixedTermSyntax.substituted_rename, termValue_rename]

theorem from_data {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w a f A j n q x y i I : Fin m) (v : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (ForcingConditionRebind.data w a f A j n q v))
    (hx : Derives Γ (SyntaxVariableSyntax.code bound w i x))
    (hi : Derives Γ (.mem i (SyntaxTermSyntax.limit bound a f))) (hs : Derives Γ (ForcingOpenLift.step bound i I)) :
    Derives Γ (equation bound w a f A j x y i I v) := by
  have hb := Derives.conjL (.conjR hd)
  have hf := Derives.conjL (.conjR (.conjR hd))
  have hLists : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a f A f (v 3) (v 5)) := .conjI
    (SyntaxMixedImageCodeFields.term_list w (v 2) a A f (v 3) (.conjR hb))
    (SyntaxMixedImageCodeFields.term_list w (v 4) f A f (v 5) (.conjR hf))
  have ht := SyntaxCodedMixedTermFields.at_field hZ bound w (v 3) (v 5) a f A f x y i hw hLists hx
  cases bound with
  | true =>
    have he := SyntaxMixedImageCodeFields.edges w (v 2) a A f (v 3) i y (.conjR hb)
    have hshift := SyntaxVariableTableFields.shifted_at hZ true w a A f (v 2) i I y (.conjL hb) hi hs
    exact SyntaxTypeLocalTransfer.iff_trans ht (SyntaxTypeLocalTransfer.iff_trans (.conjI (.conjR he) (.conjL he)) hshift)
  | false =>
    have he := SyntaxMixedImageCodeFields.edges w (v 4) f A f (v 5) i y (.conjR hf)
    have hLaw : Derives Γ ((GraphSyntax.edge (v 4) i y).iff ((Formula.mem i f).conj (ForcingConditionRebind.value w j (v 1) i y))) :=
      of_eq (by simp only [Formula.instantiate, Formula.iff, Formula.rename,
        GraphSyntax.edge_rename, ForcingConditionRebind.value_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
        (Derives.allE y (Derives.allE i (.conjR (.conjL hf))))
    have hv := AbstractTopVariablePoint.remove_scope hi (.conjI (.conjR hLaw) (.conjL hLaw))
    exact SyntaxTypeLocalTransfer.iff_trans ht (SyntaxTypeLocalTransfer.iff_trans
      (.conjI (.conjR he) (.conjL he)) (.conjI (.conjR hv) (.conjL hv)))

private def resultBody {m} (bound : Bool) (w a f A j n q x y i I : Fin m) : Formula (m+6) :=
  (ForcingConditionRebind.data (old 6 w) (old 6 a) (old 6 f) (old 6 A) (old 6 j) (old 6 n) (old 6 q) (slot 6)).conj
    (equation bound (old 6 w) (old 6 a) (old 6 f) (old 6 A) (old 6 j) (old 6 x) (old 6 y) (old 6 i) (old 6 I) (slot 6))

/-- Preserve all six real compiler witnesses and the complete original
formula-substitution judgment while deriving its actual term action. -/
def result {m} (bound : Bool) (w a f A j n q x y i I : Fin m) : Formula m :=
  existsMany 6 (resultBody bound w a f A j n q x y i I)

theorem result_rename {m l} (bound : Bool) (w a f A j n q x y i I : Fin m) (r : Fin m → Fin l) :
    (result bound w a f A j n q x y i I).rename r = result bound (r w) (r a) (r f) (r A) (r j) (r n) (r q) (r x) (r y) (r i) (r I) := by
  simp only [result, existsMany_rename, resultBody, Formula.rename, ForcingConditionRebind.data_rename,
    equation_rename, lift_old, lift_slot]

private theorem intro_result {m} {Γ : Context m} (bound : Bool) (w a f A j n q x y i I : Fin m) (v : Fin 6 → Fin m)
    (hd : Derives Γ (ForcingConditionRebind.data w a f A j n q v))
    (he : Derives Γ (equation bound w a f A j x y i I v)) : Derives Γ (result bound w a f A j n q x y i I) := by
  apply HornBinderRules.intro_many 6 _ v
  exact of_eq (by simp only [resultBody, Formula.rename, ForcingConditionRebind.data_rename, equation_rename, assign_old, assign_slot]) (.conjI hd he)

theorem derive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w a f A j n q x y i I : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (ForcingConditionRebind.compiled w a f A j n q))
    (hx : Derives Γ (SyntaxVariableSyntax.code bound w i x))
    (hi : Derives Γ (.mem i (SyntaxTermSyntax.limit bound a f))) (hs : Derives Γ (ForcingOpenLift.step bound i I)) :
    Derives Γ (result bound w a f A j n q x y i I) := by
  let D := ForcingConditionRebind.data (old 6 w) (old 6 a) (old 6 f) (old 6 A) (old 6 j) (old 6 n) (old 6 q) (slot 6)
  let Δ := Context.add D (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 D _ hc
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have he := from_data (HornBinderRules.zf_body 6 hZ D) bound (old 6 w) (old 6 a) (old 6 f) (old 6 A) (old 6 j) (old 6 n) (old 6 q)
    (old 6 x) (old 6 y) (old 6 i) (old 6 I) (slot 6)
    (of_eq (omega_rename w (old 6)) (HornBinderRules.under_body 6 hw D)) hD
    (of_eq (SyntaxVariableSyntax.code_rename bound w i x (old 6)) (HornBinderRules.under_body 6 hx D))
    (of_eq (by simp only [Formula.rename, SyntaxTermSyntax.limit_map]) (HornBinderRules.under_body 6 hi D))
    (of_eq (ForcingOpenLift.step_rename bound i I (old 6)) (HornBinderRules.under_body 6 hs D))
  exact of_eq (result_rename bound w a f A j n q x y i I (old 6)).symm
    (intro_result bound (old 6 w) (old 6 a) (old 6 f) (old 6 A) (old 6 j) (old 6 n) (old 6 q)
      (old 6 x) (old 6 y) (old 6 i) (old 6 I) (slot 6) hD he)

def input {m} (bound : Bool) (w a f A j n q x i I : Fin m) : Formula m :=
  (omega w).conj ((ForcingConditionRebind.compiled w a f A j n q).conj
    ((SyntaxVariableSyntax.code bound w i x).conj ((Formula.mem i (SyntaxTermSyntax.limit bound a f)).conj (ForcingOpenLift.step bound i I))))

def sentence {m} (bound : Bool) (w a f A j n q x y i I : Fin m) : Source.Sentence :=
  ((input bound w a f A j n q x i I).imp (result bound w a f A j n q x y i I)).close

theorem kernel_certificate {m} (bound : Bool) (w a f A j n q x y i I : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence bound w a f A j n q x y i I)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input bound w a f A j n q x i I
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact derive (ZFContext.add (ZFContext.source_ZF m) E) bound w a f A j n q x y i I
    (.conjL h) (.conjL (.conjR h)) (.conjL (.conjR (.conjR h)))
    (.conjL (.conjR (.conjR (.conjR h)))) (.conjR (.conjR (.conjR (.conjR h))))

end PPAC.Migration.ForcingRebindTerms
