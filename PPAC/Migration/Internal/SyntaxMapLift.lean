import PPAC.Migration.Internal.SyntaxMapLiftSyntax

/-! 原映射自然码的提升实际存在；同一输入码的输出码唯一并恢复原提升图。 -/
namespace PPAC.Migration.Internal.SyntaxMapLift
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxMapCodeSyntax SyntaxIndexLiftSyntax SyntaxMapLiftSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_source {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a c k u v l : Fin m)
    (hk : Derives Γ (encoded w r a c k)) (hl : Derives Γ (codedLift w a c k u v l)) :
    Derives Γ (outputAt w r a c u v l) := by
  let B := body w a c k u v l
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_lift w a c k u v l _ hl
  have hk2 : Derives Δ (encoded w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc k.castSucc.castSucc) := by
    simpa only [Formula.raise, encoded_rename] using OrderedPairElimination.under_two hk B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hEq := SyntaxMapCode.unique_graph (ZFContext.under_two hZ B) _ _ _ _ _ _ (.conjL hB) hk2
  have hLift := source_graph_subst _ _ _ _ _ _ _ _ hEq (.conjL (.conjR hB))
  have ho : Derives Δ (outputAt w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc
      u.castSucc.castSucc v.castSucc.castSucc l.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    simp only [Formula.instantiate, Formula.rename, lifted_rename, encoded_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hLift (.conjR (.conjR hB))
  simpa only [Formula.raise, outputAt_rename] using ho

theorem exists_at_source {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a c k u v : Fin m)
    (hw : Derives Γ (omega w)) (hk : Derives Γ (encoded w r a c k))
    (hu : Derives Γ (successor u a)) (hv : Derives Γ (successor v c)) :
    Derives Γ (existsLiftCode w a c k u v) := by
  have he := SyntaxIndexLift.exists_lift hZ w r a c u v hw (.conjR hk) hu hv
  let G := lifted w.castSucc r.castSucc a.castSucc c.castSucc u.castSucc v.castSucc (Fin.last m)
  let Ξ := Context.add G (Context.image Formula.raise Γ)
  change Derives Γ (.ex G) at he
  apply Derives.exE he
  have hZ1 := ZFContext.under hZ G
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw G
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have hc := SyntaxMapCodeExistence.exists_code hZ1 w.castSucc (Fin.last m) u.castSucc v.castSucc hw1 (SyntaxIndexLift.target_map _ _ _ _ _ _ _ hG)
  let L := encoded w.castSucc.castSucc (Fin.last m).castSucc u.castSucc.castSucc v.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add L (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex L) at hc
  apply Derives.exE hc
  have hk2 : Derives Δ (encoded w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc k.castSucc.castSucc) := by
    simpa only [Formula.raise, encoded_rename] using under (under hk G) L
  have hg2 : Derives Δ (lifted w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc
      u.castSucc.castSucc v.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [G, Formula.raise, lifted_rename] using under hG L
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hl := intro_lift _ _ _ _ _ _ _ _ _ hk2 hg2 hL
  have ho : Derives Δ (existsLiftCode w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc k.castSucc.castSucc u.castSucc.castSucc v.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    simpa only [Formula.instantiate, codedLift_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hl
  simpa only [Formula.raise, existsLiftCode_rename] using ho

theorem exists_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c k u v : Fin m)
    (hw : Derives Γ (omega w)) (hk : Derives Γ (mapCode w a c k))
    (hu : Derives Γ (successor u a)) (hv : Derives Γ (successor v c)) : Derives Γ (existsLiftCode w a c k u v) := by
  let R := encoded w.castSucc (Fin.last m) a.castSucc c.castSucc k.castSucc
  let Δ := Context.add R (Context.image Formula.raise Γ)
  change Derives Γ (.ex R) at hk
  apply Derives.exE hk
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw R
  have hu1 : Derives Δ (successor u.castSucc a.castSucc) := by simpa only [Formula.raise, successor_rename] using under hu R
  have hv1 : Derives Δ (successor v.castSucc c.castSucc) := by simpa only [Formula.raise, successor_rename] using under hv R
  have ho := exists_at_source (ZFContext.under hZ R) w.castSucc (Fin.last m) a.castSucc c.castSucc k.castSucc u.castSucc v.castSucc hw1 (.hyp (Or.inl rfl)) hu1 hv1
  simpa only [Formula.raise, existsLiftCode_rename] using ho

theorem unique_at_source {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a c k u v l q : Fin m)
    (hw : Derives Γ (omega w)) (hk : Derives Γ (encoded w r a c k))
    (hl : Derives Γ (codedLift w a c k u v l)) (hq : Derives Γ (codedLift w a c k u v q)) : Derives Γ (.equal l q) := by
  have he := at_source hZ w r a c k u v l hk hl
  let G := (lifted w.castSucc r.castSucc a.castSucc c.castSucc u.castSucc v.castSucc (Fin.last m)).conj
    (encoded w.castSucc (Fin.last m) u.castSucc v.castSucc l.castSucc)
  let Ξ := Context.add G (Context.image Formula.raise Γ)
  change Derives Γ (.ex G) at he
  apply Derives.exE he
  have hk1 : Derives Ξ (encoded w.castSucc r.castSucc a.castSucc c.castSucc k.castSucc) := by simpa only [Formula.raise, encoded_rename] using under hk G
  have hq1 : Derives Ξ (codedLift w.castSucc a.castSucc c.castSucc k.castSucc u.castSucc v.castSucc q.castSucc) := by simpa only [Formula.raise, codedLift_rename] using under hq G
  have hEq := at_source (ZFContext.under hZ G) _ _ _ _ _ _ _ _ hk1 hq1
  let H := (lifted w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc
    u.castSucc.castSucc v.castSucc.castSucc (Fin.last (m+1))).conj
      (encoded w.castSucc.castSucc (Fin.last (m+1)) u.castSucc.castSucc v.castSucc.castSucc q.castSucc.castSucc)
  let Δ := Context.add H (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex H) at hEq
  apply Derives.exE hEq
  have hZ2 := ZFContext.under (ZFContext.under hZ G) H
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw G) H
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have hg2 : Derives Δ (lifted w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc
      u.castSucc.castSucc v.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [G, Formula.raise, lifted_rename] using under (.conjL hG) H
  have hl2 : Derives Δ (encoded w.castSucc.castSucc (Fin.last m).castSucc u.castSucc.castSucc v.castSucc.castSucc l.castSucc.castSucc) := by
    simpa only [G, Formula.raise, encoded_rename] using under (.conjR hG) H
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hGraphs := SyntaxIndexLift.unique hZ2 _ _ _ _ _ _ _ _ hg2 (.conjL hH)
  have heL := graph_subst _ _ _ _ _ _ hGraphs hl2
  exact SyntaxMapCode.unique_code hZ2 _ _ _ _ _ _ hw2 heL (.conjR hH)
end PPAC.Migration.Internal.SyntaxMapLift
