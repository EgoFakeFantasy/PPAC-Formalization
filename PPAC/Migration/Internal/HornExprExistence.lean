import PPAC.Migration.Internal.HornExprRange

/-! 原Pairing/Union及算术构造每个固定上游表达式的实际内部求值，不抽取Type见证。 -/
namespace PPAC.Migration.Internal.HornExprExistence
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem exists_value {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (e : Expr n) (w : Fin m) (env : Fin n → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env)) : Derives Γ (existsValue e w env) := by
  induction e generalizing m with
  | literal k => exact SyntaxNumerals.exists_numeral hZ k w hw
  | var i => exact intro_existsValue (.var i) w (env i) env (environmentNat_at w env hn i) (.conjI (environmentNat_at w env hn i) (.eqRefl (env i)))
  | succ e ih =>
    have hx := ih hZ w env hw hn
    let X := (Formula.mem (Fin.last m) w.castSucc).conj (graph e w.castSucc (fun i => (env i).castSucc) (Fin.last m))
    let Δ := Context.add X (Context.image Formula.raise Γ)
    apply Derives.exE (p := X) hx
    have hZ1 := ZFContext.under hZ X
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw X)
    have hX : Derives Δ X := .hyp (Or.inl rfl)
    have hs := InsertExistence.exists_insert (Fin.last m) (Fin.last m) (ZFContext.arithmetic hZ1).base.pairing (ZFContext.arithmetic hZ1).base.union
    let S := successor (Fin.last (m+1)) (Fin.last m).castSucc
    let Ξ := Context.add S (Context.image Formula.raise Δ)
    apply Derives.exE (p := S) hs
    have hZ2 := ZFContext.under hZ1 S
    have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 S)
    have hX2 : Derives Ξ ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj (graph e w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) (Fin.last m).castSucc)) := of_eq
      (by simp only [X, Formula.raise, Formula.rename, graph_rename]) (under hX S)
    have hS : Derives Ξ S := .hyp (Or.inl rfl)
    have hy := OmegaStructureAlgebra.successor_member w.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc (ZFContext.arithmetic hZ2).base.extensionality hw2 (.conjL hX2) hS
    have ho := intro_existsValue (.succ e) w.castSucc.castSucc (Fin.last (m+1)) (fun i => (env i).castSucc.castSucc) hy
      (intro_succ e _ _ _ _ (.conjR hX2) hS)
    exact of_eq (by simp only [Formula.raise, existsValue_rename]) ho
  | pair e f ihe ihf =>
    have hx := ihe hZ w env hw hn
    let X := (Formula.mem (Fin.last m) w.castSucc).conj (graph e w.castSucc (fun i => (env i).castSucc) (Fin.last m))
    let Δ := Context.add X (Context.image Formula.raise Γ)
    apply Derives.exE (p := X) hx
    have hZ1 := ZFContext.under hZ X
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw X)
    have hn1 : Derives Δ (environmentNat n w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename n w env Fin.castSucc) (under hn X)
    have hX : Derives Δ X := .hyp (Or.inl rfl)
    have ht := ihf hZ1 w.castSucc (fun i => (env i).castSucc) hw1 hn1
    let Y := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (graph f w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) (Fin.last (m+1)))
    let Ξ := Context.add Y (Context.image Formula.raise Δ)
    apply Derives.exE (p := Y) ht
    have hZ2 := ZFContext.under hZ1 Y
    have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 Y)
    have hX2 : Derives Ξ ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj (graph e w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) (Fin.last m).castSucc)) := of_eq
      (by simp only [X, Formula.raise, Formula.rename, graph_rename]) (under hX Y)
    have hY : Derives Ξ Y := .hyp (Or.inl rfl)
    have hp := GodelPairCore.exists_code hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 (.conjL hX2) (.conjL hY)
    let P := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj (GodelPairSyntax.code w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)))
    let Ω := Context.add P (Context.image Formula.raise Ξ)
    apply Derives.exE (p := P) hp
    have hX3 : Derives Ω ((Formula.mem (Fin.last m).castSucc.castSucc w.castSucc.castSucc.castSucc).conj (graph e w.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc) (Fin.last m).castSucc.castSucc)) := of_eq
      (by simp only [Formula.raise, Formula.rename, graph_rename]) (under hX2 P)
    have hY3 : Derives Ω ((Formula.mem (Fin.last (m+1)).castSucc w.castSucc.castSucc.castSucc).conj (graph f w.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc) (Fin.last (m+1)).castSucc)) := of_eq
      (by simp only [Y, Formula.raise, Formula.rename, graph_rename]) (under hY P)
    have hP : Derives Ω P := .hyp (Or.inl rfl)
    have ho := intro_existsValue (.pair e f) w.castSucc.castSucc.castSucc (Fin.last (m+2)) (fun i => (env i).castSucc.castSucc.castSucc) (.conjL hP)
      (intro_pair e f _ _ _ _ _ (.conjR hX3) (.conjR hY3) (.conjR hP))
    exact of_eq (by simp only [Formula.raise, existsValue_rename]) ho

end PPAC.Migration.Internal.HornExprExistence
