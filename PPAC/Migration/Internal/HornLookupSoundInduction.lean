import PPAC.Migration.Internal.HornLookupSoundPoint

/-! 原Foundation及Separation在内部ω上关闭任意闭合轨迹的可靠性，不要求外部有限或标准。 -/
namespace PPAC.Migration.Internal.HornLookupSoundInduction
open Source SourceAlgebra SourceLogic OmegaSyntax HornLookupSoundSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def matrix : Formula 3 := property (0 : Fin 2).castSucc (1 : Fin 2).castSucc (Fin.last 2)

def curried {m} (w R n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) n.castSucc).imp (property w.castSucc R.castSucc (Fin.last m))))

theorem matrix_pred {m} (ρ : Fin 2 → Fin m) (x : Fin m) : MinimalPredicates.pred matrix ρ x = property (ρ 0) (ρ 1) x := by
  simp only [matrix, MinimalPredicates.pred, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem curried_rename {m k} (w R n : Fin m) (ρ : Fin m → Fin k) :
    (curried w R n).rename ρ = curried (ρ w) (ρ R) (ρ n) := by
  simp only [curried, Formula.rename, property_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem earlier_of_curried {m} {Γ : Context m} (w R n : Fin m) (hc : Derives Γ (curried w R n)) : Derives Γ (earlier w R n) := by
  apply Derives.allI
  apply Derives.impI
  let C := (Formula.mem (Fin.last m) w.castSucc).conj (.mem (Fin.last m) n.castSucc)
  let Δ := Context.add C (Context.image Formula.raise Γ)
  have hc1 : Derives Δ (curried w.castSucc R.castSucc n.castSucc) := of_eq (curried_rename w R n Fin.castSucc) (under hc C)
  have hh : Derives Δ ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) n.castSucc).imp (property w.castSucc R.castSucc (Fin.last m)))) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE (Fin.last m) hc1)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  exact .impE (.impE hh (.conjL hC)) (.conjR hC)

theorem progressive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 2 → Fin m)
    (hw : Derives Γ (omega (ρ 0))) (hc : Derives Γ (closed (ρ 0) (ρ 1))) :
    Derives Γ (BoundedInduction.progressive matrix ρ (ρ 0)) := by
  simp only [BoundedInduction.progressive, BoundedInduction.below, matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) (ρ 0).castSucc
  let I := curried (ρ 0).castSucc (ρ 1).castSucc (Fin.last m)
  let Δ := Context.add I (Context.add M (Context.image Formula.raise Γ))
  have hZ1 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.rename hZ Fin.castSucc) M) I
  have hw1 : Derives Δ (omega (ρ 0).castSucc) := of_eq (omega_rename (ρ 0) Fin.castSucc) (add (add (Derives.rename Fin.castSucc hw) M) I)
  have hc1 : Derives Δ (closed (ρ 0).castSucc (ρ 1).castSucc) := of_eq (closed_rename (ρ 0) (ρ 1) Fin.castSucc) (add (add (Derives.rename Fin.castSucc hc) M) I)
  have he := earlier_of_curried (ρ 0).castSucc (ρ 1).castSucc (Fin.last m) (Derives.hyp (Or.inl rfl) : Derives Δ I)
  exact HornLookupSoundPoint.property_from_earlier hZ1 _ _ _ hw1 hc1 he

theorem all_properties {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 2 → Fin m)
    (hw : Derives Γ (omega (ρ 0))) (hc : Derives Γ (closed (ρ 0) (ρ 1))) :
    Derives Γ (.all ((Formula.mem (Fin.last m) (ρ 0).castSucc).imp (property (ρ 0).castSucc (ρ 1).castSucc (Fin.last m)))) := by
  have hh := BoundedInduction.induction_on_set matrix ρ (ρ 0)
    (ZFContext.separation hZ matrix.neg) (ZFContext.arithmetic hZ).base.foundation (progressive hZ ρ hw hc)
  exact of_eq (by simp only [BoundedInduction.holds, matrix_pred, paramsUp]) hh

theorem at_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (closed w R)) (hn : Derives Γ (.mem n w)) : Derives Γ (property w R n) := by
  have hall := all_properties hZ (Source.SetLanguage.args2 w R)
    (by simpa only [PairSyntax.args2_first] using hw)
    (by simpa only [PairSyntax.args2_first, PairSyntax.args2_second] using hc)
  have hh : Derives Γ ((Formula.mem n w).imp (property w R n)) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, PairSyntax.args2_first, PairSyntax.args2_second, id_eq]) (Derives.allE n hall)
  exact .impE hh hn

theorem sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R n i y r : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (closed w R)) (hr : Derives Γ (HornLookupRowSyntax.row w n i y r))
    (hm : Derives Γ (.mem r R)) : Derives Γ (LookupTableExecutionSyntax.executed w n i y) :=
  property_at w R n i y r (at_natural hZ w R n hw hc (.conjL (HornLookupRowSyntax.naturals hZ w n i y r hw hr))) hr hm

end PPAC.Migration.Internal.HornLookupSoundInduction
