import PPAC.Migration.Internal.PacketTokenSyntax

/-! All token node fields and the real addConst-128 expression retain their actual values. -/
namespace PPAC.Migration.Internal.PacketTokenExpr
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax PacketTokenSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation
open YesMetaZFC.Automation.ObjectHorn (Expr)

theorem variable_row_iff {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (indices : Fin 3 → Fin n)
    (w r : Fin m) (env : Fin n → Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env)) :
    Derives Γ ((graph (ObjectPacket.node tag (List.ofFn (fun i => Expr.var (indices i)))) w env r).iff
      (tagRow tag w (env (indices 0)) (env (indices 1)) (env (indices 2)) r)) := by
  have hh := HornExprConstructor.constructor_iff hZ 3 tag (fun i => Expr.var (indices i)) w r env
    (fun i => env (indices i)) hw hn (fun i => .conjI (environmentNat_at w env hn (indices i)) (.eqRefl _))
  have he : (fun i => env (indices i)) = SyntaxAtomSyntax.three (env (indices 0)) (env (indices 1)) (env (indices 2)) := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun l => Fin.cases rfl (fun i => Fin.elim0 i) l) j) i
  rw [he] at hh
  exact hh

theorem variable_premise_iff {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (indices : Fin 3 → Fin n)
    (w V : Fin m) (env : Fin n → Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env)) :
    Derives Γ ((HornRuleSyntax.premise (ObjectPacket.node tag (List.ofFn (fun i => Expr.var (indices i)))) w V env).iff
      (tagEntry tag w V (env (indices 0)) (env (indices 1)) (env (indices 2)))) := by
  apply FormulaCodeCongruence.ex_congr
  have hw1 := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  have hn1 := of_eq (environmentNat_rename n w env Fin.castSucc) (Derives.rename Fin.castSucc hn)
  exact FormulaCodeCongruence.conj_congr
    (variable_row_iff (ZFContext.rename hZ Fin.castSucc) tag indices w.castSucc (Fin.last m)
      (fun i => (env i).castSucc) hw1 hn1) (SyntaxTypeLocalTransfer.iff_refl _)

def shiftedFields : Fin 3 → Expr 6 := Fin.cases (ObjectPacket.Expr.addConst 128 (.var 3))
  (Fin.cases (.var 5) (Fin.cases (.var 2) Fin.elim0))

theorem shifted_row_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B y r : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env))
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hy : Derives Γ (NaturalAdditionSyntax.sum w (env 3) B y)) :
    Derives Γ ((graph (ObjectPacket.node 1 [ObjectPacket.Expr.addConst 128 (.var 3),.var 5,.var 2]) w env r).iff
      (tagRow 1 w y (env 5) (env 2) r)) := by
  have hv (i : Fin 6) : Derives Γ (graph (.var i) w env (env i)) := .conjI (environmentNat_at w env hn i) (.eqRefl _)
  have hY := HornExprAddConst.backward hZ 128 (.var (3 : Fin 6)) w (env 3) B y env hw hn (hv 3) hB hy
  have hf : ∀ i, Derives Γ (graph (shiftedFields i) w env (SyntaxAtomSyntax.three y (env 5) (env 2) i)) := by
    intro i
    exact Fin.cases hY (fun j => Fin.cases (hv 5) (fun l => Fin.cases (hv 2) (fun i => Fin.elim0 i) l) j) i
  exact HornExprConstructor.constructor_iff hZ 3 1 shiftedFields w r env _ hw hn hf

theorem shifted_premise_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B y V : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env))
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hy : Derives Γ (NaturalAdditionSyntax.sum w (env 3) B y)) :
    Derives Γ ((HornRuleSyntax.premise (ObjectPacket.node 1 [ObjectPacket.Expr.addConst 128 (.var 3),.var 5,.var 2]) w V env).iff
      (tagEntry 1 w V y (env 5) (env 2))) := by
  apply FormulaCodeCongruence.ex_congr
  have hw1 := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  have hn1 := of_eq (environmentNat_rename 6 w env Fin.castSucc) (Derives.rename Fin.castSucc hn)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B Fin.castSucc) (Derives.rename Fin.castSucc hB)
  have hy1 := of_eq (NaturalAdditionSyntax.sum_rename w (env 3) B y Fin.castSucc) (Derives.rename Fin.castSucc hy)
  exact FormulaCodeCongruence.conj_congr
    (shifted_row_iff (ZFContext.rename hZ Fin.castSucc) w.castSucc B.castSucc y.castSucc (Fin.last m)
      (fun i => (env i).castSucc) hw1 hn1 hB1 hy1) (SyntaxTypeLocalTransfer.iff_refl _)

end PPAC.Migration.Internal.PacketTokenExpr
