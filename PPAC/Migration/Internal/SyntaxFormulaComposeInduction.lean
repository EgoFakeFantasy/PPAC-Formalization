import PPAC.Migration.Internal.SyntaxFormulaComposePoint

/-! 原 Foundation/Separation 在全内部ω上关闭14参数公式复合归纳；不保留 Earlier 前提。 -/
namespace PPAC.Migration.Internal.SyntaxFormulaComposeInduction
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxFormulaComposeSyntax
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def matrix : Formula 2 := property (0 : Fin 1).castSucc (Fin.last 1)

def curried {m} (w n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) n.castSucc).imp (property w.castSucc (Fin.last m))))

theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (x : Fin m) : MinimalPredicates.pred matrix ρ x = property (ρ 0) x := by
  simp only [matrix, MinimalPredicates.pred, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem curried_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (curried w n).rename ρ = curried (ρ w) (ρ n) := by
  simp only [curried, Formula.rename, property_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem earlier_of_curried {m} {Γ : Context m} (w n : Fin m) (hc : Derives Γ (curried w n)) : Derives Γ (earlier w n) := by
  apply Derives.allI
  apply Derives.impI
  let C := (Formula.mem (Fin.last m) w.castSucc).conj (.mem (Fin.last m) n.castSucc)
  let Δ := Context.add C (Context.image Formula.raise Γ)
  have hc1 : Derives Δ (curried w.castSucc n.castSucc) := of_eq (curried_rename w n Fin.castSucc) (under hc C)
  have hh : Derives Δ ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) n.castSucc).imp (property w.castSucc (Fin.last m)))) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE (Fin.last m) hc1)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  exact .impE (.impE hh (.conjL hC)) (.conjR hC)

theorem progressive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (BoundedInduction.progressive matrix (fun _ : Fin 1 => w) w) := by
  simp only [BoundedInduction.progressive, BoundedInduction.below, matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) w.castSucc
  let I := curried w.castSucc (Fin.last m)
  let Δ := Context.add I (Context.add M (Context.image Formula.raise Γ))
  have hZ1 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.rename hZ Fin.castSucc) M) I
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (add (add (Derives.rename Fin.castSucc hw) M) I)
  have he := earlier_of_curried w.castSucc (Fin.last m) (Derives.hyp (Or.inl rfl) : Derives Δ I)
  exact SyntaxFormulaComposePoint.property_from_earlier hZ1 w.castSucc (Fin.last m) hw1 he

theorem all_properties {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc (Fin.last m)))) := by
  have hh := BoundedInduction.induction_on_set matrix (fun _ : Fin 1 => w) w
    (ZFContext.separation hZ matrix.neg) (ZFContext.arithmetic hZ).base.foundation (progressive hZ w hw)
  exact of_eq (by simp only [BoundedInduction.holds, matrix_pred, paramsUp]) hh

theorem at_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) : Derives Γ (property w n) := by
  have hp : Derives Γ ((Formula.mem n w).imp (property w n)) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.allE n (all_properties hZ w hw))
  exact .impE hp hn

theorem forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S T U K L a b c d e f n q v : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (SyntaxComposeCodeSyntax.coded w a c e R T K))
    (hf : Derives Γ (SyntaxComposeCodeSyntax.coded w b d f S U L))
    (h1 : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q))
    (h2 : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v)) :
    Derives Γ (result w K L a b e f n v) :=
  .impE (property_at w n R S T U K L a b c d e f q v (at_natural hZ w n hw (.conjL h1))) (.conjI hb (.conjI hf (.conjI h1 h2)))
end PPAC.Migration.Internal.SyntaxFormulaComposeInduction
