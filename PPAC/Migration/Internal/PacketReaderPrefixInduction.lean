import PPAC.Migration.Internal.PacketReaderPrefixStep

/-! Original full Separation and Foundation discharge every actual smaller-byte-input-code prefix assumption, including all internal nonstandard codes. -/
namespace PPAC.Migration.Internal.PacketReaderPrefixInduction
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderPrefixSyntax
open ReplacementPredicates (paramsUp)
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem progressive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z)) :
    Derives Γ (BoundedInduction.progressive PacketReaderPrefixSyntax.matrix
      (PacketVarintPrefixRecursionSyntax.four w B z o) w) := by
  simp only [BoundedInduction.progressive,BoundedInduction.below,
    PacketReaderPrefixSyntax.matrix_pred,paramsUp,PacketVarintPrefixRecursionSyntax.four]
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let N := Formula.mem (Fin.last m) w.castSucc
  let I := earlier w.castSucc B.castSucc z.castSucc o.castSucc (Fin.last m)
  let Δ := Context.add I (Context.add N (Context.image Formula.raise Γ))
  have hZ1 := ZFContext.add (ZFContext.add (ZFContext.rename hZ Fin.castSucc) N) I
  have lift1 {φ : Formula m} (hh : Derives Γ φ) : Derives Δ φ.raise :=
    add (add (Derives.rename Fin.castSucc hh) N) I
  have hw1 : Derives Δ (omega w.castSucc) := by
    simpa only [Formula.raise,omega_rename] using lift1 hw
  have hB1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B.castSucc) := by
    simpa only [Formula.raise,SyntaxNumeralSyntax.numeral_rename] using lift1 hB
  have hz1 : Derives Δ (empty z.castSucc) := by
    simpa only [Formula.raise,empty_rename] using lift1 hz
  have ho1 : Derives Δ (successor o.castSucc z.castSucc) := by
    simpa only [Formula.raise,successor_rename] using lift1 ho
  exact PacketReaderPrefixStep.property_from_earlier hZ1 w.castSucc B.castSucc z.castSucc
    o.castSucc (Fin.last m) hw1 hB1 hz1 ho1 (.hyp (Or.inl rfl))

theorem all_properties {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z)) :
    Derives Γ (allProperties w B z o) := by
  have h := BoundedInduction.induction_on_set PacketReaderPrefixSyntax.matrix
    (PacketVarintPrefixRecursionSyntax.four w B z o) w
    (ZFContext.separation hZ PacketReaderPrefixSyntax.matrix.neg)
    (ZFContext.arithmetic hZ).base.foundation (progressive hZ w B z o hw hB hz ho)
  have h0 : PacketVarintPrefixRecursionSyntax.four w B z o (0 : Fin 4) = w := rfl
  have h1 : PacketVarintPrefixRecursionSyntax.four w B z o (1 : Fin 4) = B := rfl
  have h2 : PacketVarintPrefixRecursionSyntax.four w B z o (2 : Fin 4) = z := rfl
  have h3 : PacketVarintPrefixRecursionSyntax.four w B z o (3 : Fin 4) = o := rfl
  simpa only [allProperties,BoundedInduction.holds,PacketReaderPrefixSyntax.matrix_pred,
    paramsUp,h0,h1,h2,h3] using h

theorem at_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hL : Derives Γ (.mem L w)) : Derives Γ (property w B z o L) := by
  have h : Derives Γ ((Formula.mem L w).imp (property w B z o L)) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,property_rename,
      Fin.lastCases_last,Fin.lastCases_castSucc,id_eq])
      (Derives.allE L (all_properties hZ w B z o hw hB hz ho))
  exact .impE h hL

theorem extract_prefix {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w B z o L v s A O p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hBytes : Derives Γ (PacketByteInputSyntax.byteList w L))
    (hState : Derives Γ (PacketReaderStepSyntax.state w L v s A))
    (hPositive : Derives Γ (empty s).neg) (hNonempty : Derives Γ (StructuralListSyntax.nilCode w L).neg)
    (hEval : Derives Γ (PacketReaderEvalSyntax.eval w B z o L v s A p))
    (hSome : Derives Γ (PacketReaderReturnSyntax.some w O p)) :
    Derives Γ (result w B z o L v s A p) := by
  have hProperty := at_code hZ w B z o L hw hB hz ho (PacketByteInputLaws.natural w L hBytes)
  have hCase := at_fields w B z o L v s A O p hProperty
  exact .impE (.impE (.impE (.impE (.impE (.impE hCase hBytes) hState) hPositive)
    hNonempty) hEval) hSome

end PPAC.Migration.Internal.PacketReaderPrefixInduction
