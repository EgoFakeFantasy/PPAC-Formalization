import PPAC.Migration.Internal.AbstractVariableSpecialization
import PPAC.Migration.Internal.SyntaxTopCodedEnvironmentFields
import PPAC.Migration.Internal.TermTransformProgramVariable

/-! mode1零深度数值分支与实际AbstractFreeTop两张原自然码表逐点对齐。 -/
namespace PPAC.Migration.Internal.AbstractTopVariablePoint
open Source SourceAlgebra SourceLogic OmegaSyntax AbstractVariableValueSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem remove_scope {m} {Γ : Context m} {p q r : Formula m} (hp : Derives Γ p)
    (he : Derives Γ ((p.conj q).iff r)) : Derives Γ (q.iff r) := by
  apply Derives.conjI
  · exact .impI (.impE (add (.conjL he) _) (.conjI (add hp _) (.hyp (Or.inl rfl))))
  · exact .impI (.conjR (.impE (add (.conjR he) _) (.hyp (Or.inl rfl))))

theorem code_index_iff {m} {Γ : Context m} (bound : Bool) (w i j y : Fin m) (he : Derives Γ (.equal i j)) :
    Derives Γ ((SyntaxVariableSyntax.code bound w i y).iff (SyntaxVariableSyntax.code bound w j y)) := by
  apply Derives.conjI
  · exact .impI (AbstractVariableIndex.code_index_subst bound w i j y (add he _) (.hyp (Or.inl rfl)))
  · exact .impI (AbstractVariableIndex.code_index_subst bound w j i y (add (eq_symm he) _) (.hyp (Or.inl rfl)))

theorem bound_at_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z a b A B R S i j x y : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S))
    (hi : Derives Γ (.mem i a)) (hj : Derives Γ (successor j i)) :
    Derives Γ ((boundValue w z i x y).iff (StructuralListFieldSyntax.field w R i y)) := by
  have hin := SyntaxTopCodedEnvironmentTyping.abstract_input w a b A B R S he
  have hiw := StructuralListTraceOrder.member_member hZ w i a hw (.conjL (.conjL hin)) hi
  have hn := AbstractVariableSpecialization.bound_zero_iff hZ w z i j x y hw hz hiw hj
  have hf := remove_scope hi (SyntaxTopCodedEnvironmentFields.abstract_bound hZ w a b A B R S i j y he hi hj)
  exact SyntaxTypeLocalTransfer.iff_trans hn (.conjI (.conjR hf) (.conjL hf))

theorem free_at_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z a b A B R S i y : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S))
    (hi : Derives Γ (.mem i B)) (hiz : Derives Γ (empty i)) :
    Derives Γ ((freeValue w z i y).iff (StructuralListFieldSyntax.field w S i y)) := by
  have hn := AbstractVariableSpecialization.free_zero_iff w z i y hiz
  have hzi := OmegaUniversal.empty_unique i z (ZFContext.arithmetic hZ).base.extensionality hiz hz
  have hc := code_index_iff true w i z y hzi
  have hf := remove_scope hi (SyntaxTopCodedEnvironmentFields.abstract_zero hZ w a b A B R S i y hw he hiz)
  exact SyntaxTypeLocalTransfer.iff_trans hn (SyntaxTypeLocalTransfer.iff_trans (.conjI (.conjR hc) (.conjL hc)) (.conjI (.conjR hf) (.conjL hf)))

theorem free_at_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z a b A B R S i j y : Fin m)
    (hw : Derives Γ (omega w))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S))
    (hi : Derives Γ (.mem i B)) (hj : Derives Γ (successor i j)) :
    Derives Γ ((freeValue w z i y).iff (StructuralListFieldSyntax.field w S i y)) := by
  have hin := SyntaxTopCodedEnvironmentTyping.abstract_input w a b A B R S he
  have hb := Derives.conjR (.conjL hin)
  have hB := Derives.conjR (.conjR hin)
  have hjb := SyntaxIndexLiftOrder.predecessor_member hZ w b B i j hw hb hB hi hj
  have hjw := StructuralListTraceOrder.member_member hZ w j b hw hb hjb
  have hn := AbstractVariableSpecialization.free_successor_iff hZ w z i j y hw hjw hj
  have hf := remove_scope hi (SyntaxTopCodedEnvironmentFields.abstract_free hZ w a b A B R S i j y hw he hjb hj)
  exact SyntaxTypeLocalTransfer.iff_trans hn (.conjI (.conjR hf) (.conjL hf))

end PPAC.Migration.Internal.AbstractTopVariablePoint
