import PPAC.Migration.Internal.SyntaxFreeShiftGraph

/-! 位移完整图的实际原自然码、任意解码识别及全内部码唯一性。 -/
namespace PPAC.Migration.Internal.SyntaxFreeShiftCode
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxMapCodeSyntax
open SyntaxFreeShiftSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem map_subst {m} {Γ : Context m} (w b B r s : Fin m)
    (he : Derives Γ (.equal r s)) (hr : Derives Γ (shiftMap w b B r)) : Derives Γ (shiftMap w b B s) := by
  let P := shiftMap w.castSucc b.castSucc B.castSucc (Fin.last m)
  have e0 : P.instantiate r = shiftMap w b B r := by simp only [P, Formula.instantiate, shiftMap_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate s = shiftMap w b B s := by simp only [P, Formula.instantiate, shiftMap_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hr))

theorem map_code {m} {Γ : Context m} (w b B S : Fin m) (hc : Derives Γ (shiftCode w b B S)) :
    Derives Γ (mapCode w b B S) := by
  let G := (encoded w.castSucc (Fin.last m) b.castSucc B.castSucc S.castSucc).conj
    (shiftMap w.castSucc b.castSucc B.castSucc (Fin.last m))
  let Δ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) hc
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have ho := SyntaxMapCodeSyntax.intro_code w.castSucc (Fin.last m) b.castSucc B.castSucc S.castSucc (.conjL hG)
  exact of_eq (mapCode_rename w b B S Fin.castSucc).symm ho

theorem input {m} {Γ : Context m} (w b B S : Fin m) (hc : Derives Γ (shiftCode w b B S)) :
    Derives Γ ((Formula.mem b w).conj (successor B b)) := by
  let G := (encoded w.castSucc (Fin.last m) b.castSucc B.castSucc S.castSucc).conj
    (shiftMap w.castSucc b.castSucc B.castSucc (Fin.last m))
  let Δ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) hc
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hm := Derives.conjL (.conjR (.conjR hG))
  exact of_eq (by simp only [Formula.raise, Formula.rename, successor_rename])
    (Derives.conjI (.conjL (.conjL hm)) (.conjL (.conjR hG)))

theorem natural {m} {Γ : Context m} (w b B S : Fin m) (hc : Derives Γ (shiftCode w b B S)) :
    Derives Γ (.mem S w) := by
  let G := (encoded w.castSucc (Fin.last m) b.castSucc B.castSucc S.castSucc).conj
    (shiftMap w.castSucc b.castSucc B.castSucc (Fin.last m))
  let Δ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) hc
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  exact SyntaxMapCode.code_natural _ _ _ _ _ (.conjL hG)

theorem at_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b B S r : Fin m)
    (hc : Derives Γ (shiftCode w b B S)) (hr : Derives Γ (encoded w r b B S)) : Derives Γ (shiftMap w b B r) := by
  let G := (encoded w.castSucc (Fin.last m) b.castSucc B.castSucc S.castSucc).conj
    (shiftMap w.castSucc b.castSucc B.castSucc (Fin.last m))
  let Δ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) hc
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hr1 : Derives Δ (encoded w.castSucc r.castSucc b.castSucc B.castSucc S.castSucc) :=
    of_eq (encoded_rename w r b B S Fin.castSucc) (under hr G)
  have he := SyntaxMapCode.unique_graph (ZFContext.under hZ G) w.castSucc (Fin.last m) r.castSucc b.castSucc B.castSucc S.castSucc (.conjL hG) hr1
  exact of_eq (shiftMap_rename w b B r Fin.castSucc).symm (map_subst _ _ _ _ _ he (.conjR hG))

theorem encoded_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b B S r : Fin m)
    (hr : Derives Γ (encoded w r b B S)) : Derives Γ ((shiftCode w b B S).iff (shiftMap w b B r)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact at_graph (ZFContext.add hZ _) w b B S r (.hyp (Or.inl rfl)) (add hr _)
  · apply Derives.impI
    exact intro_code w b B r S (add hr _) (.hyp (Or.inl rfl))

theorem exists_at_map {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b B r : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (shiftMap w b B r)) : Derives Γ (SyntaxFreeShiftSyntax.existsCode w b B) := by
  have he := SyntaxMapCodeExistence.exists_code hZ w r b B hw (.conjL (.conjR hm))
  let K := encoded w.castSucc r.castSucc b.castSucc B.castSucc (Fin.last m)
  let Δ := Context.add K (Context.image Formula.raise Γ)
  apply Derives.exE (p := K) he
  have hm1 : Derives Δ (shiftMap w.castSucc b.castSucc B.castSucc r.castSucc) := of_eq (shiftMap_rename w b B r Fin.castSucc) (under hm K)
  have hc := intro_code w.castSucc b.castSucc B.castSucc r.castSucc (Fin.last m) (.hyp (Or.inl rfl)) hm1
  have ho : Derives Δ (SyntaxFreeShiftSyntax.existsCode w.castSucc b.castSucc B.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, shiftCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc
  exact of_eq (SyntaxFreeShiftSyntax.existsCode_rename w b B Fin.castSucc).symm ho

theorem exists_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b B : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hB : Derives Γ (successor B b)) :
    Derives Γ (SyntaxFreeShiftSyntax.existsCode w b B) := by
  let G := shiftMap w.castSucc b.castSucc B.castSucc (Fin.last m)
  let Δ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) (SyntaxFreeShiftGraph.exists_map hZ w b B hw hb hB)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw G)
  have ho := exists_at_map (ZFContext.under hZ G) _ _ _ _ hw1 (.hyp (Or.inl rfl))
  exact of_eq (SyntaxFreeShiftSyntax.existsCode_rename w b B Fin.castSucc).symm ho

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b B S T : Fin m)
    (hw : Derives Γ (omega w)) (hS : Derives Γ (shiftCode w b B S)) (hT : Derives Γ (shiftCode w b B T)) :
    Derives Γ (.equal S T) := by
  let G := (encoded w.castSucc (Fin.last m) b.castSucc B.castSucc S.castSucc).conj
    (shiftMap w.castSucc b.castSucc B.castSucc (Fin.last m))
  let Ξ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) hS
  have ht1 : Derives Ξ (shiftCode w.castSucc b.castSucc B.castSucc T.castSucc) := of_eq (shiftCode_rename w b B T Fin.castSucc) (under hT G)
  let H := (encoded w.castSucc.castSucc (Fin.last (m+1)) b.castSucc.castSucc B.castSucc.castSucc T.castSucc.castSucc).conj
    (shiftMap w.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc (Fin.last (m+1)))
  let Δ := Context.add H (Context.image Formula.raise Ξ)
  apply Derives.exE (p := H) ht1
  have hZ2 := ZFContext.under (ZFContext.under hZ G) H
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw G) H)
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have hg2 : Derives Δ ((encoded w.castSucc.castSucc (Fin.last m).castSucc b.castSucc.castSucc B.castSucc.castSucc S.castSucc.castSucc).conj
      (shiftMap w.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc)) :=
    of_eq (by simp only [G, Formula.raise, Formula.rename, encoded_rename, shiftMap_rename]) (under hG H)
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have he := SyntaxFreeShiftGraph.unique_map hZ2 _ _ _ _ _ (.conjR hg2) (.conjR hH)
  have hs2 := SyntaxMapCodeSyntax.graph_subst _ _ _ _ _ _ he (.conjL hg2)
  exact SyntaxMapCode.unique_code hZ2 _ _ _ _ _ _ hw2 hs2 (.conjL hH)
end PPAC.Migration.Internal.SyntaxFreeShiftCode
