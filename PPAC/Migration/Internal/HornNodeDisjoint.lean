import PPAC.Migration.Internal.OriginalScalarPositive

/-! 任意两个不同原节点标签的对象排斥；不局限于lookup的tag0。 -/
namespace PPAC.Migration.Internal.HornNodeDisjoint
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornApplicationSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr Rule)

theorem node_contradiction {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag target k : Nat) (hk : tag ≠ target) (payload : Expr n)
    (w row : Fin m) (env : Fin n → Fin m) (xs : Fin k → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env))
    (hy : Derives Γ (graph (.succ (.pair (.literal tag) payload)) w env row))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor k target w xs row)) : Derives Γ .bot := by
  have ht := SyntaxNumerals.exists_numeral hZ tag w hw
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral tag (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) ht
  have hZ1 := ZFContext.under hZ T
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw T)
  have hn1 : Derives Δ (environmentNat n w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename n w env Fin.castSucc) (under hn T)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hp := HornExprExistence.exists_value hZ1 payload w.castSucc (fun i => (env i).castSucc) hw1 hn1
  let P := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (graph payload w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) (Fin.last (m+1)))
  let Ξ := Context.add P (Context.image Formula.raise Δ)
  apply Derives.exE (p := P) hp
  have hZ2 := ZFContext.under hZ1 P
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 P)
  have hn2 : Derives Ξ (environmentNat n w.castSucc.castSucc (fun i => (env i).castSucc.castSucc)) := of_eq (environmentNat_rename n w.castSucc (fun i => (env i).castSucc) Fin.castSucc) (under hn1 P)
  have hy2 : Derives Ξ (graph (.succ (.pair (.literal tag) payload)) w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) row.castSucc.castSucc) := of_eq
    (by simp only [Formula.raise, graph_rename]) (under (under hy T) P)
  have hc2 : Derives Ξ (SyntaxNodeSyntax.constructor k target w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) row.castSucc.castSucc) := of_eq
    (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename]) (under (under hc T) P)
  have hT2 : Derives Ξ ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj (SyntaxNumeralSyntax.numeral tag (Fin.last m).castSucc)) := of_eq
    (by simp only [T, Formula.raise, Formula.rename, SyntaxNumeralSyntax.numeral_rename]) (under hT P)
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  have hr := Derives.impE (.conjL (HornExprStructural.raw_iff hZ2 (.literal tag) payload w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) row.castSucc.castSucc (fun i => (env i).castSucc.castSucc) hw2 hn2 (.conjR hT2) (.conjR hP))) hy2
  let C := SyntaxNodeSyntax.constructorBody k target w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) row.castSucc.castSucc
  let Ω := Context.add C (Context.image Formula.raise Ξ)
  apply Derives.exE (p := C) hc2
  have hZ3 := ZFContext.under hZ2 C
  have hw3 : Derives Ω (omega w.castSucc.castSucc.castSucc) := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 C)
  have hT3 : Derives Ω ((Formula.mem (Fin.last m).castSucc.castSucc w.castSucc.castSucc.castSucc).conj (SyntaxNumeralSyntax.numeral tag (Fin.last m).castSucc.castSucc)) := of_eq
    (by simp only [Formula.raise, Formula.rename, SyntaxNumeralSyntax.numeral_rename]) (under hT2 C)
  have hp3 : Derives Ω (.mem (Fin.last (m+1)).castSucc w.castSucc.castSucc.castSucc) := under (.conjL hP) C
  have hr3 : Derives Ω (StructuralNodeSyntax.raw w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc row.castSucc.castSucc.castSucc) := of_eq
    (StructuralNodeSyntax.raw_rename _ _ _ _ Fin.castSucc) (under hr C)
  have hC : Derives Ω C := .hyp (Or.inl rfl)
  have heq := SyntaxNodeInjective.raw_tag_eq hZ3 k _ _ _ _ _ _ hw3 (.conjL hT3) hp3 (.conjR hC) hr3
  exact .impE (SyntaxNumerals.different hZ3 target tag (Ne.symm hk) _ _ (.conjL hC) (.conjR hT3)) heq

end PPAC.Migration.Internal.HornNodeDisjoint
