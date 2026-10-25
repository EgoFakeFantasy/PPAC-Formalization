import PPAC.Migration.Internal.PacketReaderReturnRunExistence

/-! Actual history endpoint determinism and actual coded-return uniqueness give a complete object EX/ALL return fiber. -/
namespace PPAC.Migration.Internal.PacketReaderReturnRunUnique
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderReturnCodedSyntax PacketReaderHistorySyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem on_histories {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r t l d k e f g p q : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hf : Derives Γ (history w B z o n r l d f)) (hg : Derives Γ (history w B z o n t k e g))
    (hp : Derives Γ (coded w B z o r p)) (hq : Derives Γ (coded w B z o t q)) : Derives Γ (.equal p q) := by
  have hF := PacketReaderReturnRunExistence.halted_history hZ w B z o n r l d f p hw hB hf hp
  have hG := PacketReaderReturnRunExistence.halted_history hZ w B z o n t k e g q hw hB hg hq
  have he := PacketReaderStoppingUnique.endpoints hZ w B z o n r t l d k e f g hw hB hF hG
  have hq' := PacketReaderReturnTransport.coded_source w B z o t r q (eq_symm he) hq
  exact PacketReaderReturnCoded.unique hZ w B z o r p q hw hp hq'

theorem compare_with_run {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f p q : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hh : Derives Γ (history w B z o n r l d f))
    (hp : Derives Γ (coded w B z o r p)) (hq : Derives Γ (run w B z o n q)) : Derives Γ (.equal p q) := by
  let R := runBody w B z o n q
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hq
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ4 := HornBinderRules.zf_body 4 hZ R
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw R)
  have hB4 : Derives Δ (.mem (old 4 B) (old 4 w)) := HornBinderRules.under_body 4 hB R
  have hh4 := of_eq (history_rename w B z o n r l d f (old 4)) (HornBinderRules.under_body 4 hh R)
  have hp4 := of_eq (coded_rename w B z o r p (old 4)) (HornBinderRules.under_body 4 hp R)
  exact on_histories hZ4 (old 4 w) (old 4 B) (old 4 z) (old 4 o) (old 4 n) (old 4 r) (slot 4 0) (old 4 l) (old 4 d) (slot 4 1) (slot 4 2) (old 4 f) (slot 4 3) (old 4 p) (old 4 q) hw4 hB4 hh4 (.conjL hR) hp4 (.conjR hR)

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n p q : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hp : Derives Γ (run w B z o n p)) (hq : Derives Γ (run w B z o n q)) : Derives Γ (.equal p q) := by
  let R := runBody w B z o n p
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hp
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ4 := HornBinderRules.zf_body 4 hZ R
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw R)
  have hB4 : Derives Δ (.mem (old 4 B) (old 4 w)) := HornBinderRules.under_body 4 hB R
  have hq4 := of_eq (run_rename w B z o n q (old 4)) (HornBinderRules.under_body 4 hq R)
  exact compare_with_run hZ4 (old 4 w) (old 4 B) (old 4 z) (old 4 o) (old 4 n) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) (old 4 p) (old 4 q) hw4 hB4 (.conjL hR) (.conjR hR) hq4

theorem natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n q : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (run w B z o n q)) : Derives Γ (.mem q w) := by
  let R := runBody w B z o n q
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ4 := HornBinderRules.zf_body 4 hZ R
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw R)
  exact PacketReaderReturnCoded.natural hZ4 _ _ _ _ _ _ hw4 (.conjR hR)

theorem exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (.mem o w))
    (hc : Derives Γ (PacketReaderStateSyntax.carrier w n)) : Derives Γ (runFiber w B z o n) := by
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (run w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (PacketReaderReturnRunExistence.exists_run hZ w B z o n hw hB hz ho hc)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hu : Derives Δ (.all ((run w.castSucc.castSucc B.castSucc.castSucc z.castSucc.castSucc o.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let T := run w.castSucc.castSucc B.castSucc.castSucc z.castSucc.castSucc o.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))
    let Ξ := Context.add T (Context.image Formula.raise Δ)
    have hZ2 := ZFContext.under (ZFContext.under hZ R) T
    have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise,omega_rename]) (under (under hw R) T)
    have hB2 : Derives Ξ (.mem B.castSucc.castSucc w.castSucc.castSucc) := under (under hB R) T
    have hOld := of_eq (run_rename w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc (Fin.last m) Fin.castSucc) (under (.conjR hR) T)
    exact unique hZ2 _ _ _ _ _ _ _ hw2 hB2 (.hyp (Or.inl rfl)) hOld
  have hout : Derives Δ (runFiber w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [R,Formula.instantiate,Formula.rename,run_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hR hu)
  simpa only [Formula.raise,runFiber_rename] using hout

end PPAC.Migration.Internal.PacketReaderReturnRunUnique
