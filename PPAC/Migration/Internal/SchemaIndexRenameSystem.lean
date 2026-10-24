import PPAC.Migration.Internal.SchemaIndexCoded
import PPAC.Migration.Internal.SyntaxRenameOutputClassify

/-! Actual bound/free codes and uniform full-formula renaming for each schema site. -/
namespace PPAC.Migration.Internal.SchemaIndexRenameSystem
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax SchemaIndexSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def law {m} (site : Fin 3) (w : Fin m) (scopes : Fin 4 → Fin m) (R S z : Fin m) : Formula m := .all
  ((FormulaCodeSyntax.formulaCode w.castSucc (Fin.last m) (sourceScope site scopes).castSucc z.castSucc).imp
    (SyntaxRenameOutputSyntax.fiber w.castSucc R.castSucc S.castSucc (sourceScope site scopes).castSucc z.castSucc
      (targetScope site scopes).castSucc z.castSucc (Fin.last m)))

def system {m} (site : Fin 3) (w n z : Fin m) (scopes : Fin 4 → Fin m) (g R S : Fin m) : Formula m :=
  (codedState site w n scopes g R).conj ((SyntaxIdentityMapSyntax.identityCode w z S).conj (law site w scopes R S z))

def systemBody {m} (site : Fin 3) (w n z : Fin m) : Formula (m+7) :=
  system site (old 7 w) (old 7 n) (old 7 z) (fun i => slot 7 i.castSucc.castSucc.castSucc)
    (slot 7 (Fin.last 4).castSucc.castSucc) (slot 7 (Fin.last 5).castSucc) (slot 7 (Fin.last 6))

def existsSystem {m} (site : Fin 3) (w n z : Fin m) : Formula m := existsMany 7 (systemBody site w n z)

theorem law_rename {m l} (site : Fin 3) (w : Fin m) (scopes : Fin 4 → Fin m) (R S z : Fin m) (ρ : Fin m → Fin l) :
    (law site w scopes R S z).rename ρ = law site (ρ w) (fun i => ρ (scopes i)) (ρ R) (ρ S) (ρ z) := by
  simp only [law, Formula.rename, FormulaCodeSyntax.formulaCode_rename, SyntaxRenameOutputSyntax.fiber_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, sourceScope_map, targetScope_map]

theorem system_rename {m l} (site : Fin 3) (w n z : Fin m) (scopes : Fin 4 → Fin m) (g R S : Fin m) (ρ : Fin m → Fin l) :
    (system site w n z scopes g R S).rename ρ = system site (ρ w) (ρ n) (ρ z) (fun i => ρ (scopes i)) (ρ g) (ρ R) (ρ S) := by
  simp only [system, Formula.rename, codedState_rename, SyntaxIdentityMapSyntax.identityCode_rename, law_rename]

theorem systemBody_lift {m l} (site : Fin 3) (w n z : Fin m) (ρ : Fin m → Fin l) :
    (systemBody site w n z).rename (lift 7 ρ) = systemBody site (ρ w) (ρ n) (ρ z) := by
  simp only [systemBody, system_rename, lift_old, lift_slot]

theorem existsSystem_rename {m l} (site : Fin 3) (w n z : Fin m) (ρ : Fin m → Fin l) :
    (existsSystem site w n z).rename ρ = existsSystem site (ρ w) (ρ n) (ρ z) := by
  simp only [existsSystem, existsMany_rename, systemBody_lift]

theorem law_proved {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (site : Fin 3) (w : Fin m)
    (scopes : Fin 4 → Fin m) (g R S z : Fin m) (hw : Derives Γ (omega w))
    (hR : Derives Γ (SyntaxMapCodeSyntax.encoded w g (sourceScope site scopes) (targetScope site scopes) R))
    (hS : Derives Γ (SyntaxIdentityMapSyntax.identityCode w z S)) : Derives Γ (law site w scopes R S z) := by
  have hmR := SyntaxMapCodeSyntax.intro_code w g (sourceScope site scopes) (targetScope site scopes) R hR
  have hmS := SyntaxIdentityCode.map_code w z S hS
  apply Derives.allI
  have hZ1 := ZFContext.rename hZ Fin.castSucc
  have hw1 := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  have hmR1 := of_eq (SyntaxMapCodeSyntax.mapCode_rename w (sourceScope site scopes) (targetScope site scopes) R Fin.castSucc) (Derives.rename Fin.castSucc hmR)
  have hmS1 := of_eq (SyntaxMapCodeSyntax.mapCode_rename w z z S Fin.castSucc) (Derives.rename Fin.castSucc hmS)
  apply Derives.impI
  let E := FormulaCodeSyntax.formulaCode w.castSucc (Fin.last m) (sourceScope site scopes).castSucc z.castSucc
  have hi := SyntaxRenameOutputClassify.fiber_iff_input (ZFContext.add hZ1 E) w.castSucc R.castSucc S.castSucc
    (sourceScope site scopes).castSucc z.castSucc (targetScope site scopes).castSucc z.castSucc (Fin.last m) (add hw1 E)
  exact .impE (.conjR hi) (.conjI (.hyp (Or.inl rfl)) (.conjI (add hmR1 _) (add hmS1 _)))

theorem law_at {m} {Γ : Context m} (site : Fin 3) (w : Fin m) (scopes : Fin 4 → Fin m) (R S z a : Fin m)
    (hl : Derives Γ (law site w scopes R S z))
    (ha : Derives Γ (FormulaCodeSyntax.formulaCode w a (sourceScope site scopes) z)) :
    Derives Γ (SyntaxRenameOutputSyntax.fiber w R S (sourceScope site scopes) z (targetScope site scopes) z a) := by
  have hi := Derives.allE a hl
  have he : Derives Γ ((FormulaCodeSyntax.formulaCode w a (sourceScope site scopes) z).imp
      (SyntaxRenameOutputSyntax.fiber w R S (sourceScope site scopes) z (targetScope site scopes) z a)) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, FormulaCodeSyntax.formulaCode_rename,
      SyntaxRenameOutputSyntax.fiber_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hi
  exact .impE he ha

theorem intro_system {m} {Γ : Context m} (site : Fin 3) (w n z : Fin m) (scopes : Fin 4 → Fin m) (g R S : Fin m)
    (hs : Derives Γ (system site w n z scopes g R S)) : Derives Γ (existsSystem site w n z) := by
  apply HornBinderRules.intro_many 7 (systemBody site w n z) (Fin.lastCases S (Fin.lastCases R (Fin.lastCases g scopes)))
  exact of_eq (by simp only [systemBody, system_rename, assign_old, assign_slot, Fin.lastCases_last, Fin.lastCases_castSucc]) hs

theorem exists_at_coded_state {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (site : Fin 3) (w n z : Fin m)
    (scopes : Fin 4 → Fin m) (g R : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hc : Derives Γ (codedState site w n scopes g R)) : Derives Γ (existsSystem site w n z) := by
  have hzW := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  let S := SyntaxIdentityMapSyntax.identityCode w.castSucc z.castSucc (Fin.last m)
  let Δ := Context.add S (Context.image Formula.raise Γ)
  apply Derives.exE (p := S) (SyntaxIdentityCode.exists_code hZ w z hw hzW)
  have hZ1 := ZFContext.under hZ S
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw S)
  have hc1 := of_eq (codedState_rename site w n scopes g R Fin.castSucc) (under hc S)
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  have hR1 : Derives Δ (SyntaxMapCodeSyntax.encoded w.castSucc g.castSucc
      (sourceScope site (fun i => (scopes i).castSucc)) (targetScope site (fun i => (scopes i).castSucc)) R.castSucc) := .conjR hc1
  have hl := law_proved hZ1 site w.castSucc (fun i => (scopes i).castSucc) g.castSucc R.castSucc (Fin.last m) z.castSucc hw1 hR1 hS
  have ho := intro_system site w.castSucc n.castSucc z.castSucc (fun i => (scopes i).castSucc) g.castSucc R.castSucc (Fin.last m)
    (.conjI hc1 (.conjI hS hl))
  exact of_eq (existsSystem_rename site w n z Fin.castSucc).symm ho

theorem exists_system {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (site : Fin 3) (w n z : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hz : Derives Γ (empty z)) : Derives Γ (existsSystem site w n z) := by
  let B := codedBody site w n
  let Δ := Context.add B (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 B _ (SchemaIndexCoded.exists_coded_state hZ site w n hw hn)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw6 := of_eq (omega_rename w (old 6)) (HornBinderRules.under_body 6 hw B)
  have hz6 := of_eq (empty_rename z (old 6)) (HornBinderRules.under_body 6 hz B)
  have ho := exists_at_coded_state (HornBinderRules.zf_body 6 hZ B) site (old 6 w) (old 6 n) (old 6 z)
    (fun i => slot 6 i.castSucc.castSucc) (slot 6 (Fin.last 4).castSucc) (slot 6 (Fin.last 5)) hw6 hz6 hB
  exact of_eq (existsSystem_rename site w n z (old 6)).symm ho

end PPAC.Migration.Internal.SchemaIndexRenameSystem
