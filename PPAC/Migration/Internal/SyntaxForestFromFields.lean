import PPAC.Migration.Internal.SyntaxFieldsFromSlots

/-! 从实际完整字段及槽位恢复同一payload的原Forest及Constructor。 -/
namespace PPAC.Migration.Internal.SyntaxForestFromFields
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxNumeralSyntax SyntaxForestSyntax SyntaxNodeSyntax
open StructuralListLengthSyntax (hasLength hasLength_rename)
open StructuralListFieldGraphSyntax (fields fields_rename fieldsFiber)
open StructuralTreeOperatorSyntax (shape shape_rename)
open SyntaxForestFields (graphLaw graphLaw_rename law_at)
open SyntaxFieldsFromSlots (slots slots_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem included_of_laws {m} {Γ : Context m} (k : Nat) (xs : Fin k → Fin m) (g h : Fin m)
    (hg : Derives Γ (graphLaw k xs g)) (hh : Derives Γ (graphLaw k xs h)) :
    Derives Γ (GraphPointwiseSyntax.edgeIncluded g h) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hg2 : Derives Δ (graphLaw k (fun j => (xs j).castSucc.castSucc) g.castSucc.castSucc) := by
    simpa only [Formula.raise, graphLaw_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hg)
  have hh2 : Derives Δ (graphLaw k (fun j => (xs j).castSucc.castSucc) h.castSucc.castSucc) := by
    simpa only [Formula.raise, graphLaw_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hh)
  have heG := law_at k _ _ (Fin.last m).castSucc (Fin.last (m+1)) hg2
  have heH := law_at k _ _ (Fin.last m).castSucc (Fin.last (m+1)) hh2
  apply Derives.impI
  exact .impE (add (.conjR heH) _) (.impE (add (.conjL heG) _) (.hyp (Or.inl rfl)))

theorem equal_graphs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (xs : Fin k → Fin m)
    (g h d e : Fin m) (hg : Derives Γ (entriesOn g d)) (hh : Derives Γ (entriesOn h e))
    (hgl : Derives Γ (graphLaw k xs g)) (hhl : Derives Γ (graphLaw k xs h)) : Derives Γ (.equal g h) :=
  GraphPointwiseEntries.equal_of_edges g h d e (ZFContext.arithmetic hZ).base.extensionality hg hh
    (.conjI (included_of_laws k xs g h hgl hhl) (included_of_laws k xs h g hhl hgl))

theorem fields_subst_graph {m} {Γ : Context m} (w p l g h : Fin m)
    (he : Derives Γ (.equal g h)) (hf : Derives Γ (fields w p l g)) : Derives Γ (fields w p l h) := by
  have hi : Derives Γ ((fields w.castSucc p.castSucc l.castSucc (Fin.last m)).instantiate g) := by
    simpa only [Formula.instantiate, fields_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hf
  have ho := Derives.eqSubst (fields w.castSucc p.castSucc l.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, fields_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem recover {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w p l g : Fin m)
    (xs : Fin k → Fin m) (hw : Derives Γ (omega w)) (hp : Derives Γ (hasLength w p l))
    (hf : Derives Γ (fields w p l g)) (hl : Derives Γ (numeral k l))
    (hs : Derives Γ (slots k g xs)) : Derives Γ (forest k w xs p) := by
  have he := SyntaxForests.exists_forest hZ k w xs hw (SyntaxFieldsFromSlots.inputs_of_slots k w p l g xs hf hs)
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj (forest k w.castSucc (fun j => (xs j).castSucc) (Fin.last m))
  let Ξ := Context.add Q (Context.image Formula.raise Γ)
  change Derives Γ (.ex Q) at he
  apply Derives.exE he
  simp only [Formula.raise, forest_rename]
  have hZ1 := ZFContext.under hZ Q
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Q
  have hp1 : Derives Ξ (hasLength w.castSucc p.castSucc l.castSucc) := by simpa only [Formula.raise, hasLength_rename] using under hp Q
  have hf1 : Derives Ξ (fields w.castSucc p.castSucc l.castSucc g.castSucc) := by simpa only [Formula.raise, fields_rename] using under hf Q
  have hl1 : Derives Ξ (numeral k l.castSucc) := by simpa only [Formula.raise, numeral_rename] using under hl Q
  have hs1 : Derives Ξ (slots k g.castSucc (fun j => (xs j).castSucc)) := by simpa only [Formula.raise, slots_rename] using under hs Q
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have hq := SyntaxForestLength.at_numeral hZ1 k w.castSucc (fun j => (xs j).castSucc) (Fin.last m) l.castSucc hw1 (.conjR hQ) hl1
  have hx := StructuralListFieldDecode.at_length hZ1 w.castSucc (Fin.last m) l.castSucc hw1 hq
  let H := (fields w.castSucc.castSucc (Fin.last m).castSucc l.castSucc.castSucc (Fin.last (m+1))).conj
    (.all ((StructuralListFieldPairSyntax.graph w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc l.castSucc.castSucc.castSucc (Fin.last (m+2))).imp
      (.equal (Fin.last (m+2)) (Fin.last (m+1)).castSucc)))
  let Δ := Context.add H (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex H) at hx
  apply Derives.exE hx
  simp only [Formula.raise, forest_rename]
  have hZ2 := ZFContext.under hZ1 H
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 H
  have hp2 : Derives Δ (hasLength w.castSucc.castSucc p.castSucc.castSucc l.castSucc.castSucc) := by simpa only [Formula.raise, hasLength_rename] using under hp1 H
  have hf2 : Derives Δ (fields w.castSucc.castSucc p.castSucc.castSucc l.castSucc.castSucc g.castSucc.castSucc) := by simpa only [Formula.raise, fields_rename] using under hf1 H
  have hl2 : Derives Δ (numeral k l.castSucc.castSucc) := by simpa only [Formula.raise, numeral_rename] using under hl1 H
  have hs2 : Derives Δ (slots k g.castSucc.castSucc (fun j => (xs j).castSucc.castSucc)) := by simpa only [Formula.raise, slots_rename] using under hs1 H
  have hq2 : Derives Δ (hasLength w.castSucc.castSucc (Fin.last m).castSucc l.castSucc.castSucc) := by simpa only [Formula.raise, hasLength_rename] using under hq H
  have hforest : Derives Δ (forest k w.castSucc.castSucc (fun j => (xs j).castSucc.castSucc) (Fin.last m).castSucc) := by
    simpa only [Formula.raise, forest_rename] using under (.conjR hQ) H
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hgl := SyntaxFieldsFromSlots.all_edges hZ2 k _ _ _ _ _ hf2 hl2 hs2
  have hhl := SyntaxForestFields.all_edges hZ2 k _ _ _ _ _ hw2 hforest hq2 (.conjL hH)
  have heq := equal_graphs hZ2 k _ (Fin.last (m+1)) g.castSucc.castSucc l.castSucc.castSucc l.castSucc.castSucc
    (.conjL (.conjL (.conjL (.conjL hH)))) (.conjL (.conjL (.conjL hf2))) hhl hgl
  have hfields := fields_subst_graph _ _ _ _ _ heq (.conjL hH)
  have hqp := StructuralListCodeGraph.same_fields_unique hZ2 _ _ _ _ _ hw2 hq2 hp2 hfields hf2
  exact SyntaxForestInjective.output_subst k _ _ _ _ hqp hforest

theorem constructor_of_shape {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (w n t p l g : Fin m)
    (xs : Fin k → Fin m) (hw : Derives Γ (omega w)) (hd : Derives Γ (shape w n t p l g))
    (ht : Derives Γ (numeral tag t)) (hl : Derives Γ (numeral k l)) (hs : Derives Γ (slots k g xs)) :
    Derives Γ (constructor k tag w xs n) := by
  have hf := recover hZ k w p l g xs hw (.conjL (.conjR hd)) (.conjR (.conjR hd)) hl hs
  exact intro_constructor k tag w xs n t ht (intro_node k w t xs n p (.conjL (.conjL hd)) hf (.conjR (.conjL hd)))
end PPAC.Migration.Internal.SyntaxForestFromFields
