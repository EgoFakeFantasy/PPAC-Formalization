import PPAC.Migration.Internal.OriginalTermImageFields

/-! 任意内部变量作用域内，原mode0/3项轨迹与既有独立项程序逐点一致。 -/
namespace PPAC.Migration.Internal.OriginalTermProgramPoint
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem replace_at_variable {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w depth a b c L I R n q i : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (hR : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w b a c L))
    (hs : Derives Γ (.mem i (SyntaxTermSyntax.limit bound a b))) (hn : Derives Γ (SyntaxVariableSyntax.code bound w i n)) :
    Derives Γ ((OriginalTermTraceSyntax.run true w depth L n q).iff (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R L n q)) := by
  have hraw := OriginalTermTraceVariable.run_iff_value hZ true bound w depth L n i q hw hm hn
  have hprogram := TermTransformProgramVariable.at_variable hZ bound w R L n q i hw hn
  cases bound with
  | true =>
    have hfield := OriginalTermImageFields.identity_field hZ w a c I R i q hI hR hs
    have hcode := OriginalTermImageFields.code_iff_equal hZ true w i n q hw hn
    have hvalue := SyntaxTypeLocalTransfer.iff_trans hprogram (SyntaxTypeLocalTransfer.iff_trans hfield hcode)
    exact SyntaxTypeLocalTransfer.iff_trans hraw (.conjI (.conjR hvalue) (.conjL hvalue))
  | false =>
    have hpn : Derives Γ (.mem L w) := .conjL (.conjL (.conjR (.conjR hL)))
    have hlen : Derives Γ (StructuralListLengthSyntax.hasLength w L b) := .conjR (.conjL (.conjR (.conjR hL)))
    have hin := SyntaxVariableDecode.index_natural false w i n hn
    have hrun := LookupTableCorrectnessInduction.execution_iff_at_natural hZ w L i q hw hpn hin
    have hfield := StrictLookupValue.in_range_field_iff hZ w L b i q hw hlen hs
    have hexec := SyntaxTypeLocalTransfer.iff_trans hrun hfield
    have hvalue := SyntaxTypeLocalTransfer.iff_trans hprogram (.conjI (.conjR hexec) (.conjL hexec))
    exact SyntaxTypeLocalTransfer.iff_trans hraw (.conjI (.conjR hvalue) (.conjL hvalue))

theorem weaken_at_variable {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w depth parameter a b B I J R S n q i : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (OriginalTermTraceSyntax.metadata w depth parameter))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (hJ : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (hR : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a B))
    (hS : Derives Γ (IndexTermImageCodeSyntax.converted false w J S b a B))
    (hs : Derives Γ (.mem i (SyntaxTermSyntax.limit bound a b))) (hn : Derives Γ (SyntaxVariableSyntax.code bound w i n)) :
    Derives Γ ((OriginalTermTraceSyntax.run false w depth parameter n q).iff (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R S n q)) := by
  have hraw := OriginalTermTraceVariable.run_iff_value hZ false bound w depth parameter n i q hw hm hn
  have hprogram := TermTransformProgramVariable.at_variable hZ bound w R S n q i hw hn
  cases bound with
  | true =>
    have hfield := OriginalTermImageFields.identity_field hZ w a B I R i q hI hR hs
    have hcode := OriginalTermImageFields.code_iff_equal hZ true w i n q hw hn
    have hvalue := SyntaxTypeLocalTransfer.iff_trans hprogram (SyntaxTypeLocalTransfer.iff_trans hfield hcode)
    exact SyntaxTypeLocalTransfer.iff_trans hraw (.conjI (.conjR hvalue) (.conjL hvalue))
  | false =>
    have hfield := OriginalTermImageFields.shift_field hZ w a b B J S i q hJ hS hs
    have hvalue := SyntaxTypeLocalTransfer.iff_trans hprogram hfield
    exact SyntaxTypeLocalTransfer.iff_trans hraw (.conjI (.conjR hvalue) (.conjL hvalue))

end PPAC.Migration.Internal.OriginalTermProgramPoint
