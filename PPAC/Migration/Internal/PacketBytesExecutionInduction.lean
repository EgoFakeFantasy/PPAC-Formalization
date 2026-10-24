import PPAC.Migration.Internal.PacketBytesExecutionUnique

/-! Original Foundation and full Separation discharge every joint IH for actual byte execution. -/
namespace PPAC.Migration.Internal.PacketBytesExecutionInduction
open Source SourceAlgebra SourceLogic OmegaSyntax PacketBytesTraceSyntax PacketByteInputSyntax PacketBytesExecutionSyntax
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem property_from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n)) : Derives Γ (property w n) := by
  exact .conjI (PacketBytesExecutionTotal.total_property hZ w n hw hi)
    (.conjI (PacketBytesExecutionDomain.domain_property hZ w n hw hi) (PacketBytesExecutionUnique.unique_property hZ w n hw hi))

theorem progressive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (BoundedInduction.progressive PacketBytesExecutionSyntax.matrix (fun _ : Fin 1 => w) w) := by
  simp only [BoundedInduction.progressive, BoundedInduction.below, PacketBytesExecutionSyntax.matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) w.castSucc
  let I := earlier w.castSucc (Fin.last m)
  let Δ := Context.add I (Context.add M (Context.image Formula.raise Γ))
  have hZ1 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.rename hZ Fin.castSucc) M) I
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using add (add (Derives.rename Fin.castSucc hw) M) I
  exact property_from_earlier hZ1 _ _ hw1 (.hyp (Or.inl rfl))

theorem all_properties {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc (Fin.last m)))) := by
  have h := BoundedInduction.induction_on_set PacketBytesExecutionSyntax.matrix (fun _ : Fin 1 => w) w
    (ZFContext.separation hZ PacketBytesExecutionSyntax.matrix.neg) (ZFContext.arithmetic hZ).base.foundation (progressive hZ w hw)
  simpa only [BoundedInduction.holds, PacketBytesExecutionSyntax.matrix_pred, paramsUp] using h

theorem at_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) : Derives Γ (property w n) := by
  have h : Derives Γ ((Formula.mem n w).imp (property w n)) := by
    simpa only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE n (all_properties hZ w hw)
  exact .impE h hn

theorem exists_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (byteList w n)) (ht : Derives Γ (.mem t w)) : Derives Γ (existsOutput w n t) :=
  total_at w n t (at_code hZ w n hw (PacketByteInputLaws.natural w n hn)) hn ht

theorem input_domain {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (bytes w n t a)) : Derives Γ (byteList w n) :=
  domain_at w n t a (at_code hZ w n hw (PacketBytesExecutionAffine.bytes_input_natural w n t a ha)) ha

theorem output_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a b : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (bytes w n t a)) (hb : Derives Γ (bytes w n t b)) : Derives Γ (.equal a b) :=
  unique_at w n t a b (at_code hZ w n hw (PacketBytesExecutionAffine.bytes_input_natural w n t a ha)) ha hb

end PPAC.Migration.Internal.PacketBytesExecutionInduction
