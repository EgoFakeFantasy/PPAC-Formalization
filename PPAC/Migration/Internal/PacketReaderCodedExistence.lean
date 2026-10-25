import PPAC.Migration.Internal.PacketReaderCodedUnique

/-! A coded successor exists exactly on the original raw admissible domain at every actual source-state code. -/
namespace PPAC.Migration.Internal.PacketReaderCodedExistence
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderStateSyntax PacketReaderCodedSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem exists_next {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n l v s a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (.mem z w)) (ho : Derives Γ (.mem o w))
    (hc : Derives Γ (code w l v s a n)) (ha : Derives Γ (PacketReaderInputExistence.admissible w B z o l v s a)) :
    Derives Γ (existsNext w B z o n) := by
  have hex := Derives.impE (.conjR (PacketReaderInputExistence.domain_iff hZ w B z o l v s a hw hB hz ho)) ha
  let R := PacketReaderInputSyntax.resultBody w B z o l v s a
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hex
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ4 := HornBinderRules.zf_body 4 hZ R
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw R)
  have hc4 := of_eq (code_rename w l v s a n (old 4)) (HornBinderRules.under_body 4 hc R)
  have hcode := PacketReaderStateCode.exists_code hZ4 _ _ _ _ _ hw4 (.conjL hR)
  let K := (Formula.mem (Fin.last (m+4)) (old 4 w).castSucc).conj
    (code (old 4 w).castSucc (slot 4 0).castSucc (slot 4 1).castSucc (slot 4 2).castSucc (slot 4 3).castSucc (Fin.last (m+4)))
  let Ξ := Context.add K (Context.image Formula.raise Δ)
  apply Derives.exE (p := K) hcode
  have hK : Derives Ξ K := .hyp (Or.inl rfl)
  have hc5 := of_eq (code_rename (old 4 w) (old 4 l) (old 4 v) (old 4 s) (old 4 a) (old 4 n) Fin.castSucc) (under hc4 K)
  have ha5 := of_eq (PacketReaderInputSyntax.advance_rename (old 4 w) (old 4 B) (old 4 z) (old 4 o) (old 4 l) (old 4 v) (old 4 s) (old 4 a) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) Fin.castSucc) (under (.conjR hR) K)
  have hs := intro_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc5 (.conjR hK) ha5
  have hout : Derives Ξ (existsNext (old 4 w).castSucc (old 4 B).castSucc (old 4 z).castSucc (old 4 o).castSucc (old 4 n).castSucc) := by
    apply Derives.exI (Fin.last (m+4))
    exact of_eq (by simp only [Formula.instantiate,Formula.rename,step_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI (.conjL hK) hs)
  simpa only [Formula.raise,existsNext_rename] using hout

theorem domain_at_source {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n l v s a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hc : Derives Γ (code w l v s a n))
    (he : Derives Γ (existsNext w B z o n)) : Derives Γ (PacketReaderInputExistence.admissible w B z o l v s a) := by
  let K := (Formula.mem (Fin.last m) w.castSucc).conj (step w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc (Fin.last m))
  let Δ := Context.add K (Context.image Formula.raise Γ)
  apply Derives.exE (p := K) he
  have hK : Derives Δ K := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ K
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw K)
  have hc1 := of_eq (code_rename w l v s a n Fin.castSucc) (under hc K)
  have hn := Derives.impE (.conjL (PacketReaderCodedNormalize.at_source hZ1 _ _ _ _ _ _ _ _ _ _ hw1 hc1)) (.conjR hK)
  let R := nextBody w.castSucc B.castSucc z.castSucc o.castSucc l.castSucc v.castSucc s.castSucc a.castSucc (Fin.last m)
  let Ξ := Context.add R (raisedContext 4 Δ)
  apply HornBinderRules.eliminate_many 4 R _ hn
  have hR : Derives Ξ R := .hyp (Or.inl rfl)
  have hZ5 := HornBinderRules.zf_body 4 hZ1 R
  have hw5 := of_eq (omega_rename w.castSucc (old 4)) (HornBinderRules.under_body 4 hw1 R)
  have hB5 : Derives Ξ (.mem (old 4 B.castSucc) (old 4 w.castSucc)) := HornBinderRules.under_body 4 (under hB K) R
  have hraw := PacketReaderInputSyntax.intro_result _ _ _ _ _ _ _ _ _ _ _ _ (.conjL (.conjL hR)) (.conjR hR)
  have hout := PacketReaderInputExistence.result_domain hZ5 _ _ _ _ _ _ _ _ hw5 hB5 hraw
  exact of_eq (by simp only [Formula.raise,PacketReaderInputExistence.admissible_rename]) hout

theorem exists_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n l v s a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (.mem z w)) (ho : Derives Γ (.mem o w))
    (hc : Derives Γ (code w l v s a n)) :
    Derives Γ ((existsNext w B z o n).iff (PacketReaderInputExistence.admissible w B z o l v s a)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact domain_at_source (ZFContext.add hZ _) _ _ _ _ _ _ _ _ _ (add hw _) (add hB _) (add hc _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact exists_next (ZFContext.add hZ _) _ _ _ _ _ _ _ _ _ (add hw _) (add hB _) (add hz _) (add ho _) (add hc _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.PacketReaderCodedExistence
