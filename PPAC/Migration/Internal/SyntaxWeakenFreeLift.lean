import PPAC.Migration.Internal.SyntaxIdentityUnique
import PPAC.Migration.Internal.SyntaxIdentityLift

/-! 任意给定后继域恒等码反向识别成原恒等码的实际绑定提升。 -/
namespace PPAC.Migration.Internal.SyntaxWeakenFreeLift
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax
open SyntaxIdentityMapSyntax (identityCode identityCode_rename)
open SyntaxMapLiftSyntax (codedLift codedLift_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem subst_l {m} {Γ : Context m} (w a c R u v L K : Fin m)
    (he : Derives Γ (.equal L K)) (hl : Derives Γ (codedLift w a c R u v L)) :
    Derives Γ (codedLift w a c R u v K) := by
  let P := codedLift w.castSucc a.castSucc c.castSucc R.castSucc u.castSucc v.castSucc (Fin.last m)
  have e0 : P.instantiate L = codedLift w a c R u v L := by
    simp only [P, Formula.instantiate, codedLift_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate K = codedLift w a c R u v K := by
    simp only [P, Formula.instantiate, codedLift_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hl))

theorem identity_lift {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a R u L : Fin m)
    (hw : Derives Γ (omega w)) (hR : Derives Γ (identityCode w a R))
    (hu : Derives Γ (successor u a)) (hL : Derives Γ (identityCode w u L)) :
    Derives Γ (codedLift w a a R u u L) := by
  have he := SyntaxMapLift.exists_code hZ w a a R u u hw
    (SyntaxIdentityCode.map_code w a R hR) hu hu
  let K := codedLift w.castSucc a.castSucc a.castSucc R.castSucc u.castSucc u.castSucc (Fin.last m)
  let Δ := Context.add K (Context.image Formula.raise Γ)
  change Derives Γ (.ex K) at he
  apply Derives.exE (p := K) he
  have hZ1 := ZFContext.under hZ K
  have hw1 : Derives Δ (omega w.castSucc) :=
    of_eq (omega_rename w Fin.castSucc) (under hw K)
  have hR1 : Derives Δ (identityCode w.castSucc a.castSucc R.castSucc) :=
    of_eq (identityCode_rename w a R Fin.castSucc) (under hR K)
  have hL1 : Derives Δ (identityCode w.castSucc u.castSucc L.castSucc) :=
    of_eq (identityCode_rename w u L Fin.castSucc) (under hL K)
  have hK : Derives Δ K := .hyp (Or.inl rfl)
  have hi := SyntaxIdentityLift.code_same_successor hZ1 w.castSucc a.castSucc R.castSucc
    u.castSucc (Fin.last m) hw1 hR1 hK
  have hEq := SyntaxIdentityUnique.code_unique hZ1 w.castSucc u.castSucc (Fin.last m) L.castSucc
    hw1 hi hL1
  have ho := subst_l w.castSucc a.castSucc a.castSucc R.castSucc u.castSucc u.castSucc
    (Fin.last m) L.castSucc hEq hK
  exact of_eq (codedLift_rename w a a R u u L Fin.castSucc).symm ho

end PPAC.Migration.Internal.SyntaxWeakenFreeLift
