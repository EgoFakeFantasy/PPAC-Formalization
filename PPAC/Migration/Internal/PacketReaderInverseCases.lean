import PPAC.Migration.Internal.PacketReaderInverseNil
import PPAC.Migration.Internal.PacketReaderInverseCons
import PPAC.Migration.Internal.PacketReaderPrefixInduction

/-! Nil success and a genuine nonempty canonical prefix give the whole-input inverse step at zero value and unit scale. -/
namespace PPAC.Migration.Internal.PacketReaderInverseCases
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderInverseSyntax

theorem from_earlier_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L A O p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hi : Derives Γ (earlier w B z o L)) (hBytes : Derives Γ (PacketByteInputSyntax.byteList w L))
    (hEval : Derives Γ (PacketReaderEvalSyntax.eval w B z o L z o A p))
    (hSome : Derives Γ (PacketReaderReturnSyntax.some w O p)) : Derives Γ (result w L A O) := by
  apply SourcePropositional.by_cases (StructuralListSyntax.nilCode w L)
  · exact PacketReaderInverseNil.nil_case (ZFContext.add hZ _) w B z o L A O p
      (add hw _) (add hB _) (add hz _) (add ho _) (.hyp (Or.inl rfl)) (add hEval _) (add hSome _)
  · let N := (StructuralListSyntax.nilCode w L).neg
    let Δ := Context.add N Γ
    have hZ1 := ZFContext.add hZ N
    have hState := PacketReaderSuccess.state w B z o L z o A p (add hEval N)
    have hPrefix := PacketReaderPrefixInduction.extract_prefix hZ1 w B z o L z o A O p
      (add hw N) (add hB N) (add hz N) (add ho N) (add hBytes N) hState
      (add (OmegaStructureAlgebra.successor_not_empty o z ho) N) (.hyp (Or.inl rfl)) (add hEval N) (add hSome N)
    exact PacketReaderInverseCons.from_prefix hZ1 w B z o L A O p
      (add hw N) (add hB N) (add hz N) (add ho N) (add hi N) (add hEval N) (add hSome N) hPrefix

end PPAC.Migration.Internal.PacketReaderInverseCases
