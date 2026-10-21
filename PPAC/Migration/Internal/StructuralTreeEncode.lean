import PPAC.Migration.Internal.StructuralTreeShapeUnique

/-! 每个内部自然标签和完整自然值序列实际产生唯一原树码；不预设已存在代码。 -/
namespace PPAC.Migration.Internal.StructuralTreeEncode
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralTreeOperatorSyntax StructuralTreeEncodeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem exists_encoding {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w tag l f : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem tag w)) (hl : Derives Γ (.mem l w))
    (hf : Derives Γ (SequenceSyntax.sequence f l w)) : Derives Γ (existsEncoding w tag l f) := by
  have hp := StructuralListEncodeExistence.exists_encoding hZ w f l hw hf hl
  let P := StructuralListEncodeSyntax.encoding w.castSucc f.castSucc l.castSucc (Fin.last m)
  let Ξ := Context.add P (Context.image Formula.raise Γ)
  change Derives Γ (.ex P) at hp
  apply Derives.exE (p := P) hp
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ P
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw P
  have ht1 : Derives Ξ (.mem tag.castSucc w.castSucc) := under ht P
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  have hn := StructuralNodeExistence.exists_raw hZ1 w.castSucc tag.castSucc (Fin.last m) hw1 ht1 (.conjL (.conjL hP))
  let N := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (StructuralNodeSyntax.raw w.castSucc.castSucc tag.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add N (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex N) at hn
  apply Derives.exE (p := N) hn
  have hP2 : Derives Δ (StructuralListEncodeSyntax.encoding w.castSucc.castSucc f.castSucc.castSucc l.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [P, Formula.raise, StructuralListEncodeSyntax.encoding_rename] using under hP N
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hs : Derives Δ (shape w.castSucc.castSucc (Fin.last (m+1)) tag.castSucc.castSucc (Fin.last m).castSucc l.castSucc.castSucc f.castSucc.castSucc) :=
    .conjI (.conjI (under ht1 N) (.conjR hN)) (.conjI (.conjR (.conjL hP2)) (.conjR hP2))
  have hout := intro_exists _ _ _ _ _ (intro_encoding _ _ _ _ _ _ hs)
  simpa only [Formula.raise, existsEncoding_rename] using hout

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w tag l f n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (encoding w tag l f n)) : Derives Γ (.mem n w) := by
  let E := encodingBody w tag l f n
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply eliminate_encoding w tag l f n _ he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw E
  exact StructuralNodeProperties.range (ZFContext.under hZ E) _ _ _ _ hw1 (.conjR (.conjL hE))

theorem raw_payload_subst {m} {Γ : Context m} (w tag p q n : Fin m) (he : Derives Γ (.equal p q))
    (hr : Derives Γ (StructuralNodeSyntax.raw w tag p n)) : Derives Γ (StructuralNodeSyntax.raw w tag q n) := by
  have hi : Derives Γ ((StructuralNodeSyntax.raw w.castSucc tag.castSucc (Fin.last m) n.castSucc).instantiate p) := by
    simpa only [Formula.instantiate, StructuralNodeSyntax.raw_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hr
  have ho := Derives.eqSubst (StructuralNodeSyntax.raw w.castSucc tag.castSucc (Fin.last m) n.castSucc) he hi
  simpa only [Formula.instantiate, StructuralNodeSyntax.raw_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem at_payloads {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w tag l f p q n r : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (shape w n tag p l f)) (hr : Derives Γ (shape w r tag q l f)) : Derives Γ (.equal n r) := by
  have hp := StructuralListLengthBasic.code_member _ _ _ (.conjL (.conjR hn))
  have hpq := StructuralListCodeGraph.same_fields_unique hZ _ _ _ _ _ hw (.conjL (.conjR hn)) (.conjL (.conjR hr))
    (.conjR (.conjR hn)) (.conjR (.conjR hr))
  have hraw := raw_payload_subst _ _ _ _ _ (eq_symm hpq) (.conjR (.conjL hr))
  exact StructuralNodeCore.unique hZ _ _ _ _ _ hw (.conjL (.conjL hn)) hp (.conjR (.conjL hn)) hraw

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w tag l f n r : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (encoding w tag l f n)) (hr : Derives Γ (encoding w tag l f r)) : Derives Γ (.equal n r) := by
  let N := encodingBody w tag l f n
  let Ξ := Context.add N (Context.image Formula.raise Γ)
  apply eliminate_encoding w tag l f n _ hn
  have hr1 : Derives Ξ (encoding w.castSucc tag.castSucc l.castSucc f.castSucc r.castSucc) := by simpa only [Formula.raise, encoding_rename] using under hr N
  let R := encodingBody w.castSucc tag.castSucc l.castSucc f.castSucc r.castSucc
  let Δ := Context.add R (Context.image Formula.raise Ξ)
  apply eliminate_encoding w.castSucc tag.castSucc l.castSucc f.castSucc r.castSucc _ hr1
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw N) R
  have hN : Derives Ξ N := .hyp (Or.inl rfl)
  have hN2 : Derives Δ (shape w.castSucc.castSucc n.castSucc.castSucc tag.castSucc.castSucc (Fin.last m).castSucc l.castSucc.castSucc f.castSucc.castSucc) := by
    simpa only [N, encodingBody, Formula.raise, shape_rename] using under hN R
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact at_payloads (ZFContext.under (ZFContext.under hZ N) R) _ _ _ _ _ _ _ _ hw2 hN2 hR

theorem unique_formula {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w tag l f n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (encoding w tag l f n)) : Derives Γ (uniqueAt w tag l f n) := by
  apply Derives.allI
  apply Derives.impI
  let E := encoding w.castSucc tag.castSucc l.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw E
  have he1 : Derives Δ (encoding w.castSucc tag.castSucc l.castSucc f.castSucc n.castSucc) := by simpa only [Formula.raise, encoding_rename] using under he E
  exact unique (ZFContext.under hZ E) _ _ _ _ _ _ hw1 (.hyp (Or.inl rfl)) he1

theorem exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w tag l f : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem tag w)) (hl : Derives Γ (.mem l w))
    (hf : Derives Γ (SequenceSyntax.sequence f l w)) : Derives Γ (encodingFiber w tag l f) := by
  have he := exists_encoding hZ w tag l f hw ht hl hf
  let E := encoding w.castSucc tag.castSucc l.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  change Derives Γ (.ex E) at he
  apply Derives.exE (p := E) he
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ E
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw E
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hnat := range hZ1 _ _ _ _ _ hw1 hE
  have hu := unique_formula hZ1 _ _ _ _ _ hw1 hE
  have hout : Derives Δ (encodingFiber w.castSucc tag.castSucc l.castSucc f.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, encoding_rename, uniqueAt_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI (.conjI hnat hE) hu
  simpa only [Formula.raise, encodingFiber_rename] using hout
end PPAC.Migration.Internal.StructuralTreeEncode
