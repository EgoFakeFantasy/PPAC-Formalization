import PPAC.Migration.Internal.PacketReaderReturnPayload

/-! Original EOF success constructs an actual reversed payload and Some code; both rejection causes construct actual None. -/
namespace PPAC.Migration.Internal.PacketReaderReturnExistence
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderReturnSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem success_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L v s a : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (PacketReaderInputSyntax.eofSuccess w z o L v s a)) :
    Derives Γ (existsResult w B z o L v s a) := by
  have hValid := Derives.conjR (.conjR (.conjR (.conjL he)))
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (StructuralListReverseSyntax.reverses w.castSucc a.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (StructuralListReverseEncoding.exists_reverse hZ w a hw hValid)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have he1 := of_eq (PacketReaderInputSyntax.eofSuccess_rename w z o L v s a Fin.castSucc) (under he R)
  let T := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (some w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Ξ := Context.add T (Context.image Formula.raise Δ)
  apply Derives.exE (p := T) (PacketReaderReturnPayload.some_exists hZ1 w.castSucc (Fin.last m) hw1 (.conjL hR))
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have he2 := of_eq (PacketReaderInputSyntax.eofSuccess_rename w.castSucc z.castSucc o.castSucc L.castSucc v.castSucc s.castSucc a.castSucc Fin.castSucc) (under he1 T)
  have hRev := of_eq (StructuralListReverseSyntax.reverses_rename w.castSucc a.castSucc (Fin.last m) Fin.castSucc) (under (.conjR hR) T)
  have hSuccess := intro_success _ _ _ _ _ _ _ _ _ he2 hRev (.conjR hT)
  have hRet : Derives Ξ (result w.castSucc.castSucc B.castSucc.castSucc z.castSucc.castSucc o.castSucc.castSucc L.castSucc.castSucc v.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc (Fin.last (m+1))) := .disjL hSuccess
  have hout : Derives Ξ (existsResult w.castSucc.castSucc B.castSucc.castSucc z.castSucc.castSucc o.castSucc.castSucc L.castSucc.castSucc v.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Formula.instantiate,Formula.rename,result_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI (.conjL hT) hRet)
  simpa only [Formula.raise,existsResult_rename] using hout

theorem failure_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L v s a : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (rejection w B z o L v s a)) : Derives Γ (existsResult w B z o L v s a) := by
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (none w.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (PacketReaderReturnPayload.none_exists hZ w hw)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have he1 := of_eq (rejection_rename w B z o L v s a Fin.castSucc) (under he R)
  have hRet : Derives Δ (result w.castSucc B.castSucc z.castSucc o.castSucc L.castSucc v.castSucc s.castSucc a.castSucc (Fin.last m)) := .disjR (.conjI he1 (.conjR hR))
  have hout : Derives Δ (existsResult w.castSucc B.castSucc z.castSucc o.castSucc L.castSucc v.castSucc s.castSucc a.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate,Formula.rename,result_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI (.conjL hR) hRet)
  simpa only [Formula.raise,existsResult_rename] using hout

theorem from_terminal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L v s a : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (PacketReaderTerminalSyntax.raw w B z o L v s a)) :
    Derives Γ (existsResult w B z o L v s a) := by
  apply Derives.disjE he
  · exact success_exists (ZFContext.add hZ _) w B z o L v s a (add hw _) (.hyp (Or.inl rfl))
  · exact failure_exists (ZFContext.add hZ _) w B z o L v s a (add hw _) (.hyp (Or.inl rfl))

theorem domain {m} {Γ : Context m} (w B z o L v s a q : Fin m)
    (hr : Derives Γ (result w B z o L v s a q)) : Derives Γ (PacketReaderTerminalSyntax.raw w B z o L v s a) := by
  apply Derives.disjE hr
  · exact .disjL (.conjL (.hyp (Or.inl rfl)))
  · exact .disjR (.conjL (.hyp (Or.inl rfl)))

theorem exists_domain {m} {Γ : Context m} (w B z o L v s a : Fin m)
    (hr : Derives Γ (existsResult w B z o L v s a)) : Derives Γ (PacketReaderTerminalSyntax.raw w B z o L v s a) := by
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (result w.castSucc B.castSucc z.castSucc o.castSucc L.castSucc v.castSucc s.castSucc a.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  simpa only [Formula.raise,PacketReaderTerminalSyntax.raw_rename] using domain _ _ _ _ _ _ _ _ _ (.conjR hR)

theorem exact_domain {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L v s a : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((existsResult w B z o L v s a).iff (PacketReaderTerminalSyntax.raw w B z o L v s a)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact exists_domain _ _ _ _ _ _ _ _ (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact from_terminal (ZFContext.add hZ _) _ _ _ _ _ _ _ _ (add hw _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.PacketReaderReturnExistence
