import PPAC.Migration.Internal.PacketStructureSyntax

/-! Generic arity row and premise normalization retains every ordered field. -/
namespace PPAC.Migration.Internal.PacketStructureExpr
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax PacketStructureSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation
open ObjectHorn (Expr)

theorem row_at {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (exprs : Fin k → Expr n)
    (w r : Fin m) (env : Fin n → Fin m) (xs : Fin k → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env)) (hs : ∀ i, Derives Γ (graph (exprs i) w env (xs i))) :
    Derives Γ ((graph (ObjectPacket.node tag (List.ofFn exprs)) w env r).iff (row k tag w xs r)) :=
  HornExprConstructor.constructor_iff hZ k tag exprs w r env xs hw hn hs

theorem premise_at {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (exprs : Fin k → Expr n)
    (w V : Fin m) (env : Fin n → Fin m) (xs : Fin k → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env)) (hs : ∀ i, Derives Γ (graph (exprs i) w env (xs i))) :
    Derives Γ ((HornRuleSyntax.premise (ObjectPacket.node tag (List.ofFn exprs)) w V env).iff (entry k tag w V xs)) := by
  apply FormulaCodeCongruence.ex_congr
  have hw1 := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  have hn1 := of_eq (environmentNat_rename n w env Fin.castSucc) (Derives.rename Fin.castSucc hn)
  exact FormulaCodeCongruence.conj_congr
    (row_at (ZFContext.rename hZ Fin.castSucc) k tag exprs w.castSucc (Fin.last m) (fun i => (env i).castSucc)
      (fun i => (xs i).castSucc) hw1 hn1 (fun i => of_eq (graph_rename (exprs i) w (xs i) env Fin.castSucc) (Derives.rename Fin.castSucc (hs i))))
    (SyntaxTypeLocalTransfer.iff_refl _)

theorem var_graph {m n} {Γ : Context m} (w : Fin m) (env : Fin n → Fin m) (hn : Derives Γ (environmentNat n w env)) (i : Fin n) :
    Derives Γ (graph (.var i) w env (env i)) := .conjI (environmentNat_at w env hn i) (.eqRefl _)

end PPAC.Migration.Internal.PacketStructureExpr
