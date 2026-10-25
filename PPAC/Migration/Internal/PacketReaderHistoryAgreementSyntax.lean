import PPAC.Migration.Internal.PacketReaderHistoryAppend
import PPAC.Migration.Internal.SyntaxIndexLiftOrder

/-! One fixed object Formula3 compares all actual graph values at an arbitrary internal index. -/
namespace PPAC.Migration.Internal.PacketReaderHistoryAgreementSyntax
open Source SourceAlgebra SourceLogic GraphSyntax
open SyntaxRenameQuerySyntax (of_eq)

def agree {m} (f g i : Fin m) : Formula m := .all (.all
  ((edge f.castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc).imp
    ((edge g.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))).imp (.equal (Fin.last m).castSucc (Fin.last (m+1))))))
def matrix : Formula 3 := agree 0 1 2
def allAgreement {m} (w f g : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp (agree f.castSucc g.castSucc (Fin.last m)))

theorem agree_rename {m k} (f g i : Fin m) (ρ : Fin m → Fin k) :
    (agree f g i).rename ρ = agree (ρ f) (ρ g) (ρ i) := by
  simp only [agree,Formula.rename,edge_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]
theorem allAgreement_rename {m k} (w f g : Fin m) (ρ : Fin m → Fin k) :
    (allAgreement w f g).rename ρ = allAgreement (ρ w) (ρ f) (ρ g) := by
  simp only [allAgreement,Formula.rename,agree_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 2 → Fin m) (i : Fin m) : MinimalPredicates.pred matrix ρ i = agree (ρ 0) (ρ 1) i := by
  have h0 : Fin.lastCases i ρ (0 : Fin 3) = ρ 0 := by
    change Fin.lastCases i ρ (0 : Fin 2).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases i ρ (1 : Fin 3) = ρ 1 := by
    change Fin.lastCases i ρ (1 : Fin 2).castSucc = ρ 1
    exact Fin.lastCases_castSucc _
  have h2 : Fin.lastCases i ρ (2 : Fin 3) = i := by
    change Fin.lastCases i ρ (Fin.last 2) = i
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred,matrix,agree_rename,h0,h1,h2]

theorem at_values {m} {Γ : Context m} (f g i a b : Fin m) (hi : Derives Γ (agree f g i))
    (ha : Derives Γ (edge f i a)) (hb : Derives Γ (edge g i b)) : Derives Γ (.equal a b) := by
  have hp : Derives Γ ((edge f i a).imp ((edge g i b).imp (.equal a b))) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,edge_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE b (Derives.allE a hi))
  exact .impE (.impE hp ha) hb

theorem all_at {m} {Γ : Context m} (w f g i : Fin m) (hi : Derives Γ (allAgreement w f g))
    (hn : Derives Γ (.mem i w)) : Derives Γ (agree f g i) := by
  have hp : Derives Γ ((Formula.mem i w).imp (agree f g i)) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,agree_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE i hi)
  exact .impE hp hn

theorem step_source_subst {m} {Γ : Context m} (w B z o n r N : Fin m) (he : Derives Γ (.equal n N))
    (ht : Derives Γ (PacketReaderCodedSyntax.step w B z o n r)) : Derives Γ (PacketReaderCodedSyntax.step w B z o N r) := by
  let P := PacketReaderCodedSyntax.step w.castSucc B.castSucc z.castSucc o.castSucc (Fin.last m) r.castSucc
  have h0 : P.instantiate n = PacketReaderCodedSyntax.step w B z o n r := by simp only [P,Formula.instantiate,PacketReaderCodedSyntax.step_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate N = PacketReaderCodedSyntax.step w B z o N r := by simp only [P,Formula.instantiate,PacketReaderCodedSyntax.step_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm ht))

end PPAC.Migration.Internal.PacketReaderHistoryAgreementSyntax
