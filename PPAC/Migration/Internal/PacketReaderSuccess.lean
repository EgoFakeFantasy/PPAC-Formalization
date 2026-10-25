import PPAC.Migration.Internal.ObjectPacketTokensByteInput
import PPAC.Migration.Internal.PacketReaderEval
import PPAC.Migration.Internal.PacketReaderReturnNormalize

/-! Actual Some success excludes the original rejection causes and recovers the precise EOF guard and reverse payload on actual Nil input. -/
namespace PPAC.Migration.Internal.PacketReaderSuccess
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderEvalSyntax PacketReaderReturnSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem state {m} {Γ : Context m} (w B z o L v s A p : Fin m)
    (he : Derives Γ (eval w B z o L v s A p)) : Derives Γ (PacketReaderStepSyntax.state w L v s A) := by
  let R := (PacketReaderStateSyntax.code w.castSucc L.castSucc v.castSucc s.castSucc A.castSucc (Fin.last m)).conj
    (PacketReaderReturnCodedSyntax.run w.castSucc B.castSucc z.castSucc o.castSucc (Fin.last m) p.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) he
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  simpa only [Formula.raise,PacketReaderStepSyntax.state_rename] using Derives.conjL (.conjL hR)

theorem nil_terminal {m} {Γ : Context m} (w B z o L v s A : Fin m)
    (hs : Derives Γ (PacketReaderStepSyntax.state w L v s A)) (hL : Derives Γ (StructuralListSyntax.nilCode w L)) :
    Derives Γ (PacketReaderTerminalSyntax.raw w B z o L v s A) := by
  apply Derives.disjE (PacketReaderGuards.eof_partition z o v s)
  · exact .disjL (.conjI (add hs _) (.conjI (add hL _) (.hyp (Or.inl rfl))))
  · exact .disjR (.disjL (.conjI (add hs _) (.conjI (add hL _) (.hyp (Or.inl rfl)))))

theorem nil_success {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L v s A O p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hL : Derives Γ (StructuralListSyntax.nilCode w L)) (he : Derives Γ (eval w B z o L v s A p))
    (hSome : Derives Γ (some w O p)) :
    Derives Γ ((PacketReaderInputSyntax.eofSuccess w z o L v s A).conj (StructuralListReverseSyntax.reverses w A O)) := by
  have hTerminal := nil_terminal w B z o L v s A (state w B z o L v s A p he) hL
  have hReturn := Derives.impE (.conjL (PacketReaderEval.at_terminal hZ w B z o L v s A p hw hB hz ho hTerminal)) he
  exact .impE (.conjL (PacketReaderReturnNormalize.at_some hZ w B z o L v s A O p hw hSome)) hReturn

theorem nil_guard {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L v s A O p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hL : Derives Γ (StructuralListSyntax.nilCode w L)) (he : Derives Γ (eval w B z o L v s A p))
    (hSome : Derives Γ (some w O p)) : Derives Γ ((Formula.equal s o).conj (.equal v z)) :=
  .conjR (.conjR (.conjL (nil_success hZ w B z o L v s A O p hw hB hz ho hL he hSome)))

theorem nil_reverse {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L v s A O p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hL : Derives Γ (StructuralListSyntax.nilCode w L)) (he : Derives Γ (eval w B z o L v s A p))
    (hSome : Derives Γ (some w O p)) : Derives Γ (StructuralListReverseSyntax.reverses w A O) :=
  .conjR (nil_success hZ w B z o L v s A O p hw hB hz ho hL he hSome)

theorem rejection_disjoint {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L v s A O p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hr : Derives Γ (rejection w B z o L v s A)) (he : Derives Γ (eval w B z o L v s A p))
    (hSome : Derives Γ (some w O p)) : Derives Γ .bot := by
  have hTerminal : Derives Γ (PacketReaderTerminalSyntax.raw w B z o L v s A) := .disjR hr
  have hReturn := Derives.impE (.conjL (PacketReaderEval.at_terminal hZ w B z o L v s A p hw hB hz ho hTerminal)) he
  have hNone := Derives.impE (.conjL (PacketReaderFixedReturn.at_rejection hZ w B z o L v s A p hw hr)) hReturn
  exact PacketReaderReturnPayload.disjoint hZ w O p hw hNone hSome

theorem reject_at_cons {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L b X v s A O p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hHead : Derives Γ (PacketReaderInputSyntax.headRest w L b X)) (hReject : Derives Γ (PacketReaderStepSyntax.reject B z o b s))
    (he : Derives Γ (eval w B z o L v s A p)) (hSome : Derives Γ (some w O p)) : Derives Γ .bot := by
  have hBlocked := PacketReaderInputSyntax.intro_blocked w B z o L s b X hHead hReject
  have hr : Derives Γ (rejection w B z o L v s A) := .disjR (.conjI (state w B z o L v s A p he) hBlocked)
  exact rejection_disjoint hZ w B z o L v s A O p hw hB hz ho hr he hSome

theorem nonunit_not_nil {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L v s A O p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (he : Derives Γ (eval w B z o L v s A p)) (hSome : Derives Γ (some w O p))
    (hs : Derives Γ (Formula.equal s o).neg) : Derives Γ (StructuralListSyntax.nilCode w L).neg := by
  apply Derives.impI
  let H := StructuralListSyntax.nilCode w L
  have hGuard := nil_guard (ZFContext.add hZ H) w B z o L v s A O p (add hw H) (add hB H) (add hz H) (add ho H) (.hyp (Or.inl rfl)) (add he H) (add hSome H)
  exact .impE (add hs H) (.conjL hGuard)

end PPAC.Migration.Internal.PacketReaderSuccess
