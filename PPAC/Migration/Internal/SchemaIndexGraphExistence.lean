import PPAC.Migration.Internal.SchemaIndexSyntax

/-! Three actual schema graphs, built from successor maps and genuine binder lifts. -/
namespace PPAC.Migration.Internal.SchemaIndexGraphExistence
open Source SourceAlgebra SourceLogic OmegaSyntax SchemaIndexSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem separation {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m) (scopes : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hc : Derives Γ (chain n scopes)) : Derives Γ (existsGraph 0 w n scopes) := by
  let R := SchemaDoubleShiftSyntax.map w.castSucc n.castSucc (scopes 0).castSucc (scopes 1).castSucc (Fin.last m)
  let Γ1 := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (SchemaDoubleShiftGraph.exists_map hZ w n (scopes 0) (scopes 1) hw hn (.conjL hc) (.conjL (.conjR hc)))
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hR : Derives Γ1 R := .hyp (Or.inl rfl)
  have hc1 : Derives Γ1 (chain n.castSucc (fun i => (scopes i).castSucc)) := of_eq (chain_rename n scopes Fin.castSucc) (under hc R)
  let H := SyntaxIndexLiftSyntax.lifted w.castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc (scopes 1).castSucc.castSucc (scopes 0).castSucc.castSucc (scopes 2).castSucc.castSucc (Fin.last (m+1))
  let Γ2 := Context.add H (Context.image Formula.raise Γ1)
  apply Derives.exE (p := H) (SyntaxIndexLift.exists_lift hZ1 w.castSucc (Fin.last m) n.castSucc (scopes 1).castSucc (scopes 0).castSucc (scopes 2).castSucc hw1 (SchemaDoubleShiftGraph.index_map w.castSucc n.castSucc (scopes 0).castSucc (scopes 1).castSucc (Fin.last m) hR) (.conjL hc1) (.conjL (.conjR (.conjR hc1))))
  have hR2 : Derives Γ2 (SchemaDoubleShiftSyntax.map w.castSucc.castSucc n.castSucc.castSucc (scopes 0).castSucc.castSucc (scopes 1).castSucc.castSucc (Fin.last m).castSucc) := of_eq (by simp only [R, Formula.raise, SchemaDoubleShiftSyntax.map_rename]) (under hR H)
  have hH : Derives Γ2 H := .hyp (Or.inl rfl)
  have hg := intro_graph 0 w.castSucc.castSucc n.castSucc.castSucc (fun i => (scopes i).castSucc.castSucc) (Fin.last (m+1)) (Fin.last m).castSucc (Fin.last m).castSucc (.conjI hR2 (.conjI (.eqRefl _) hH))
  have ho := intro_exists_graph 0 w.castSucc.castSucc n.castSucc.castSucc (fun i => (scopes i).castSucc.castSucc) (Fin.last (m+1)) hg
  exact of_eq (by simp only [Formula.raise, existsGraph_rename]) ho

theorem collection_premise {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m) (scopes : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hc : Derives Γ (chain n scopes)) : Derives Γ (existsGraph 1 w n scopes) := by
  let R := SyntaxFreeShiftSyntax.shiftMap w.castSucc n.castSucc (scopes 0).castSucc (Fin.last m)
  let Γ1 := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (SyntaxFreeShiftGraph.exists_map hZ w n (scopes 0) hw hn (.conjL hc))
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hR : Derives Γ1 R := .hyp (Or.inl rfl)
  have hc1 : Derives Γ1 (chain n.castSucc (fun i => (scopes i).castSucc)) := of_eq (chain_rename n scopes Fin.castSucc) (under hc R)
  let H := SyntaxIndexLiftSyntax.lifted w.castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc (scopes 0).castSucc.castSucc (scopes 0).castSucc.castSucc (scopes 1).castSucc.castSucc (Fin.last (m+1))
  let Γ2 := Context.add H (Context.image Formula.raise Γ1)
  apply Derives.exE (p := H) (SyntaxIndexLift.exists_lift hZ1 w.castSucc (Fin.last m) n.castSucc (scopes 0).castSucc (scopes 0).castSucc (scopes 1).castSucc hw1 (.conjL (.conjR hR)) (.conjL hc1) (.conjL (.conjR hc1)))
  have hR2 : Derives Γ2 (SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc n.castSucc.castSucc (scopes 0).castSucc.castSucc (Fin.last m).castSucc) := of_eq (by simp only [R, Formula.raise, SyntaxFreeShiftSyntax.shiftMap_rename]) (under hR H)
  have hH : Derives Γ2 H := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 H
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 H)
  have hc2 : Derives Γ2 (chain n.castSucc.castSucc (fun i => (scopes i).castSucc.castSucc)) := of_eq (chain_rename n.castSucc (fun i => (scopes i).castSucc) Fin.castSucc) (under hc1 H)
  let G := SyntaxIndexLiftSyntax.lifted w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (scopes 0).castSucc.castSucc.castSucc (scopes 1).castSucc.castSucc.castSucc (scopes 1).castSucc.castSucc.castSucc (scopes 2).castSucc.castSucc.castSucc (Fin.last (m+2))
  let Γ3 := Context.add G (Context.image Formula.raise Γ2)
  apply Derives.exE (p := G) (SyntaxIndexLift.exists_lift hZ2 w.castSucc.castSucc (Fin.last (m+1)) (scopes 0).castSucc.castSucc (scopes 1).castSucc.castSucc (scopes 1).castSucc.castSucc (scopes 2).castSucc.castSucc hw2 (SyntaxIndexLift.target_map w.castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc (scopes 0).castSucc.castSucc (scopes 0).castSucc.castSucc (scopes 1).castSucc.castSucc (Fin.last (m+1)) hH) (.conjL (.conjR hc2)) (.conjL (.conjR (.conjR hc2))))
  have hR3 := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w.castSucc.castSucc n.castSucc.castSucc (scopes 0).castSucc.castSucc (Fin.last m).castSucc Fin.castSucc) (under hR2 G)
  have hH3 : Derives Γ3 (SyntaxIndexLiftSyntax.lifted w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc n.castSucc.castSucc.castSucc (scopes 0).castSucc.castSucc.castSucc (scopes 0).castSucc.castSucc.castSucc (scopes 1).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc) := of_eq (by simp only [H, Formula.raise, SyntaxIndexLiftSyntax.lifted_rename]) (under hH G)
  have hG : Derives Γ3 G := .hyp (Or.inl rfl)
  have hg := intro_graph 1 w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (fun i => (scopes i).castSucc.castSucc.castSucc) (Fin.last (m+2)) (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (.conjI hR3 (.conjI hH3 hG))
  have ho := intro_exists_graph 1 w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (fun i => (scopes i).castSucc.castSucc.castSucc) (Fin.last (m+2)) hg
  exact of_eq (by simp only [Formula.raise, existsGraph_rename]) ho

theorem collection_image {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m) (scopes : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hc : Derives Γ (chain n scopes)) : Derives Γ (existsGraph 2 w n scopes) := by
  let R := SchemaDoubleShiftSyntax.map w.castSucc n.castSucc (scopes 0).castSucc (scopes 1).castSucc (Fin.last m)
  let Γ1 := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (SchemaDoubleShiftGraph.exists_map hZ w n (scopes 0) (scopes 1) hw hn (.conjL hc) (.conjL (.conjR hc)))
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hR : Derives Γ1 R := .hyp (Or.inl rfl)
  have hc1 : Derives Γ1 (chain n.castSucc (fun i => (scopes i).castSucc)) := of_eq (chain_rename n scopes Fin.castSucc) (under hc R)
  let H := SyntaxIndexLiftSyntax.lifted w.castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc (scopes 1).castSucc.castSucc (scopes 0).castSucc.castSucc (scopes 2).castSucc.castSucc (Fin.last (m+1))
  let Γ2 := Context.add H (Context.image Formula.raise Γ1)
  apply Derives.exE (p := H) (SyntaxIndexLift.exists_lift hZ1 w.castSucc (Fin.last m) n.castSucc (scopes 1).castSucc (scopes 0).castSucc (scopes 2).castSucc hw1 (SchemaDoubleShiftGraph.index_map w.castSucc n.castSucc (scopes 0).castSucc (scopes 1).castSucc (Fin.last m) hR) (.conjL hc1) (.conjL (.conjR (.conjR hc1))))
  have hR2 : Derives Γ2 (SchemaDoubleShiftSyntax.map w.castSucc.castSucc n.castSucc.castSucc (scopes 0).castSucc.castSucc (scopes 1).castSucc.castSucc (Fin.last m).castSucc) := of_eq (by simp only [R, Formula.raise, SchemaDoubleShiftSyntax.map_rename]) (under hR H)
  have hH : Derives Γ2 H := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 H
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 H)
  have hc2 : Derives Γ2 (chain n.castSucc.castSucc (fun i => (scopes i).castSucc.castSucc)) := of_eq (chain_rename n.castSucc (fun i => (scopes i).castSucc) Fin.castSucc) (under hc1 H)
  let G := SyntaxIndexLiftSyntax.lifted w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (scopes 0).castSucc.castSucc.castSucc (scopes 2).castSucc.castSucc.castSucc (scopes 1).castSucc.castSucc.castSucc (scopes 3).castSucc.castSucc.castSucc (Fin.last (m+2))
  let Γ3 := Context.add G (Context.image Formula.raise Γ2)
  apply Derives.exE (p := G) (SyntaxIndexLift.exists_lift hZ2 w.castSucc.castSucc (Fin.last (m+1)) (scopes 0).castSucc.castSucc (scopes 2).castSucc.castSucc (scopes 1).castSucc.castSucc (scopes 3).castSucc.castSucc hw2 (SyntaxIndexLift.target_map w.castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc (scopes 1).castSucc.castSucc (scopes 0).castSucc.castSucc (scopes 2).castSucc.castSucc (Fin.last (m+1)) hH) (.conjL (.conjR hc2)) (.conjR (.conjR (.conjR hc2))))
  have hR3 := of_eq (SchemaDoubleShiftSyntax.map_rename w.castSucc.castSucc n.castSucc.castSucc (scopes 0).castSucc.castSucc (scopes 1).castSucc.castSucc (Fin.last m).castSucc Fin.castSucc) (under hR2 G)
  have hH3 : Derives Γ3 (SyntaxIndexLiftSyntax.lifted w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc n.castSucc.castSucc.castSucc (scopes 1).castSucc.castSucc.castSucc (scopes 0).castSucc.castSucc.castSucc (scopes 2).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc) := of_eq (by simp only [H, Formula.raise, SyntaxIndexLiftSyntax.lifted_rename]) (under hH G)
  have hG : Derives Γ3 G := .hyp (Or.inl rfl)
  have hg := intro_graph 2 w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (fun i => (scopes i).castSucc.castSucc.castSucc) (Fin.last (m+2)) (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (.conjI hR3 (.conjI hH3 hG))
  have ho := intro_exists_graph 2 w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (fun i => (scopes i).castSucc.castSucc.castSucc) (Fin.last (m+2)) hg
  exact of_eq (by simp only [Formula.raise, existsGraph_rename]) ho

theorem exists_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (site : Fin 3) (w n : Fin m) (scopes : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hc : Derives Γ (chain n scopes)) : Derives Γ (existsGraph site w n scopes) := by
  rcases site with ⟨k,hk⟩
  have h : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases h with rfl | rfl | rfl
  · exact separation hZ w n scopes hw hn hc
  · exact collection_premise hZ w n scopes hw hn hc
  · exact collection_image hZ w n scopes hw hn hc

end PPAC.Migration.Internal.SchemaIndexGraphExistence
