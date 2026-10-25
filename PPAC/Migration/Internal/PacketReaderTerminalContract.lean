import PPAC.Migration.Internal.PacketReaderTerminalHistory

/-! Classified histories retain joint endpoint, length, domain and graph uniqueness under object EX4 and ALL4. -/
namespace PPAC.Migration.Internal.PacketReaderTerminalContract
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderTerminalSyntax
open PacketReaderStoppingContract (same same_rename)
open SyntaxRenameQuerySyntax (of_eq)

def uniqueAtBody {m} (w B z o n r l d f : Fin m) : Formula (m+4) :=
  (classifiedHistory (old 4 w) (old 4 B) (old 4 z) (old 4 o) (old 4 n) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)).imp
    (same (old 4 r) (old 4 l) (old 4 d) (old 4 f) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3))

def uniqueAt {m} (w B z o n r l d f : Fin m) : Formula m :=
  (uniqueAtBody w B z o n r l d f).all.all.all.all

def uniqueClassifiedBody {m} (w B z o n : Fin m) : Formula (m+4) :=
  (classifiedHistory (old 4 w) (old 4 B) (old 4 z) (old 4 o) (old 4 n) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)).conj
    (uniqueAt (old 4 w) (old 4 B) (old 4 z) (old 4 o) (old 4 n) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3))

def uniqueClassifiedComplete {m} (w B z o n : Fin m) : Formula m := existsMany 4 (uniqueClassifiedBody w B z o n)

theorem uniqueAtBody_lift {m k} (w B z o n r l d f : Fin m) (ρ : Fin m → Fin k) :
    (uniqueAtBody w B z o n r l d f).rename (lift 4 ρ) = uniqueAtBody (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) (ρ r) (ρ l) (ρ d) (ρ f) := by
  simp only [uniqueAtBody,Formula.rename,classifiedHistory_rename,same_rename,lift_old,lift_slot]

theorem uniqueAt_rename {m k} (w B z o n r l d f : Fin m) (ρ : Fin m → Fin k) :
    (uniqueAt w B z o n r l d f).rename ρ = uniqueAt (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) (ρ r) (ρ l) (ρ d) (ρ f) := by
  change ((uniqueAtBody w B z o n r l d f).rename (lift 4 ρ)).all.all.all.all = _
  rw [uniqueAtBody_lift]
  rfl

theorem uniqueClassifiedBody_lift {m k} (w B z o n : Fin m) (ρ : Fin m → Fin k) :
    (uniqueClassifiedBody w B z o n).rename (lift 4 ρ) = uniqueClassifiedBody (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) := by
  simp only [uniqueClassifiedBody,Formula.rename,classifiedHistory_rename,uniqueAt_rename,lift_old,lift_slot]

theorem uniqueClassifiedComplete_rename {m k} (w B z o n : Fin m) (ρ : Fin m → Fin k) :
    (uniqueClassifiedComplete w B z o n).rename ρ = uniqueClassifiedComplete (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) := by
  simp only [uniqueClassifiedComplete,existsMany_rename,uniqueClassifiedBody_lift]

theorem fields_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r t l d k e f g : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hf : Derives Γ (classifiedHistory w B z o n r l d f)) (hg : Derives Γ (classifiedHistory w B z o n t k e g)) : Derives Γ (same r l d f t k e g) :=
  PacketReaderStoppingContract.fields_unique hZ w B z o n r t l d k e f g hw hB
    (PacketReaderTerminalHistory.to_halted hZ w B z o n r l d f hw hB hf)
    (PacketReaderTerminalHistory.to_halted hZ w B z o n t k e g hw hB hg)

theorem all_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hf : Derives Γ (classifiedHistory w B z o n r l d f)) : Derives Γ (uniqueAt w B z o n r l d f) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let H := classifiedHistory (old 4 w) (old 4 B) (old 4 z) (old 4 o) (old 4 n) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
  let Δ := Context.add H (raisedContext 4 Γ)
  have lift4 {p : Formula m} (hp : Derives Γ p) : Derives Δ (p.rename (old 4)) := add (HornBinderRules.under_many 4 hp) H
  have hZ4 := ZFContext.add (HornBinderRules.zf_many 4 hZ) H
  have hw4 := of_eq (omega_rename w (old 4)) (lift4 hw)
  have hB4 : Derives Δ (.mem (old 4 B) (old 4 w)) := lift4 hB
  have hf4 := of_eq (classifiedHistory_rename w B z o n r l d f (old 4)) (lift4 hf)
  exact fields_unique hZ4 (old 4 w) (old 4 B) (old 4 z) (old 4 o) (old 4 n) (old 4 r) (slot 4 0) (old 4 l) (old 4 d) (slot 4 1) (slot 4 2) (old 4 f) (slot 4 3) hw4 hB4 hf4 (.hyp (Or.inl rfl))

theorem intro_unique {m} {Γ : Context m} (w B z o n r l d f : Fin m)
    (hh : Derives Γ (classifiedHistory w B z o n r l d f)) (hu : Derives Γ (uniqueAt w B z o n r l d f)) :
    Derives Γ (uniqueClassifiedComplete w B z o n) := by
  apply HornBinderRules.intro_many 4 _ (PacketReaderStateSyntax.fields r l d f)
  exact of_eq (by simp only [uniqueClassifiedBody,Formula.rename,classifiedHistory_rename,uniqueAt_rename,assign_old,assign_slot]; rfl) (.conjI hh hu)

theorem exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (.mem o w))
    (hc : Derives Γ (PacketReaderStateSyntax.carrier w n)) : Derives Γ (uniqueClassifiedComplete w B z o n) := by
  let R := classifiedBody w B z o n
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ (PacketReaderTerminalHistory.exists_classified hZ w B z o n hw hB hz ho hc)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ4 := HornBinderRules.zf_body 4 hZ R
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw R)
  have hB4 : Derives Δ (.mem (old 4 B) (old 4 w)) := HornBinderRules.under_body 4 hB R
  have hu := all_unique hZ4 _ _ _ _ _ _ _ _ _ hw4 hB4 hR
  exact of_eq (uniqueClassifiedComplete_rename w B z o n (old 4)).symm (intro_unique _ _ _ _ _ _ _ _ _ hR hu)

end PPAC.Migration.Internal.PacketReaderTerminalContract
