import PPAC.Migration.Internal.StructuralTreeRecursion

/-! 同码实际节点数据的四分量唯一；不是宿主层解码器，也不截断内部字段序列。 -/
namespace PPAC.Migration.Internal.StructuralTreeDecode
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralTreeValiditySyntax
open StructuralListLengthSyntax (under_four zf_under_four)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem payload_subst {m} {Γ : Context m} (w n tag p q l f : Fin m) (he : Derives Γ (.equal p q))
    (hd : Derives Γ (nodeData w n tag p l f)) : Derives Γ (nodeData w n tag q l f) := by
  have hi : Derives Γ ((nodeData w.castSucc n.castSucc tag.castSucc (Fin.last m) l.castSucc f.castSucc).instantiate p) := by
    simpa only [Formula.instantiate, nodeData_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hd
  have ho := Derives.eqSubst (nodeData w.castSucc n.castSucc tag.castSucc (Fin.last m) l.castSucc f.castSucc) he hi
  simpa only [Formula.instantiate, nodeData_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem unique_pair {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n tag p l f other q k g : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (nodeData w n tag p l f)) (ho : Derives Γ (nodeData w n other q k g)) :
    Derives Γ (((Formula.equal tag other).conj (.equal p q)).conj ((Formula.equal l k).conj (.equal f g))) := by
  have hs := Derives.conjL hd
  have ht := Derives.conjL ho
  have hp := StructuralListLengthBasic.code_member _ _ _ (.conjL (.conjR hs))
  have hq := StructuralListLengthBasic.code_member _ _ _ (.conjL (.conjR ht))
  have he := StructuralNodeCore.injective hZ _ _ _ _ _ _ hw (.conjL (.conjL hs)) hp (.conjL (.conjL ht)) hq
    (.conjR (.conjL hs)) (.conjR (.conjL ht))
  have hOther := payload_subst _ _ _ _ _ _ _ (eq_symm (.conjR he)) ho
  have hSame := Derives.conjL hOther
  exact .conjI he (StructuralListFieldDecode.unique_pair hZ _ _ _ _ _ _ hw (.conjL (.conjR hs)) (.conjL (.conjR hSame))
    (.conjR (.conjR hs)) (.conjR (.conjR hSame)))

theorem unique_formula {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n tag p l f : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (nodeData w n tag p l f)) : Derives Γ (uniqueData w n tag p l f) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let D := dataBody w n
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  have hZ4 : ZFContext.Evidence Δ := zf_under_four hZ D
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under_four hw D
  have hd4 : Derives Δ (nodeData w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc
      tag.castSucc.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc.castSucc l.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, nodeData_rename] using under_four hd D
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  exact unique_pair hZ4 _ _ _ _ _ _ _ _ _ _ hw4 hD hd4

theorem intro_decoded {m} {Γ : Context m} (w n tag p l f : Fin m)
    (hd : Derives Γ (nodeData w n tag p l f)) (hu : Derives Γ (uniqueData w n tag p l f)) : Derives Γ (decodedFiber w n) := by
  apply Derives.exI tag
  apply Derives.exI p
  apply Derives.exI l
  apply Derives.exI f
  simp only [dataBody, Formula.instantiate, Formula.rename, nodeData_rename, uniqueData_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hd hu

theorem exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (valid w n)) : Derives Γ (decodedFiber w n) := by
  have hr := StructuralTreeRecursion.valid_to_recursive hZ w n hw hv
  let D := dataBody w n
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply eliminate_recursive w n _ hr
  have hZ4 : ZFContext.Evidence Δ := zf_under_four hZ D
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under_four hw D
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have hu := unique_formula hZ4 _ _ _ _ _ _ hw4 hD
  have hout := intro_decoded _ _ _ _ _ _ hD hu
  simpa only [Formula.raise, decodedFiber_rename] using hout

theorem recursive_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (recursive w n)) : Derives Γ (.mem n w) := by
  let D := dataBody w n
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply eliminate_recursive w n _ hr
  have hZ4 : ZFContext.Evidence Δ := zf_under_four hZ D
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under_four hw D
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  exact StructuralNodeProperties.range hZ4 _ _ _ _ hw4 (.conjR (.conjL (.conjL hD)))

theorem recursive_to_valid {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (recursive w n)) : Derives Γ (valid w n) :=
  .impE (.conjR (StructuralTreeRecursion.valid_iff_recursive hZ w n hw (recursive_member hZ w n hw hr))) hr

theorem recursive_iff_valid {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((recursive w n).iff (valid w n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact recursive_to_valid (ZFContext.add hZ _) _ _ (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact StructuralTreeRecursion.valid_to_recursive (ZFContext.add hZ _) _ _ (add hw _) (.hyp (Or.inl rfl))

theorem decoded_to_recursive {m} {Γ : Context m} (w n : Fin m)
    (hf : Derives Γ (decodedFiber w n)) : Derives Γ (recursive w n) := by
  let D := (dataBody w n).conj (uniqueData w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)))
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  change Derives Γ (.ex (.ex (.ex (.ex D)))) at hf
  apply Derives.exE hf
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have hout := intro_recursive _ _ _ _ _ _ (.conjL hD)
  have hflat : Derives Δ (recursive w n).raise.raise.raise.raise := by simpa only [Formula.raise, recursive_rename] using hout
  refine Derives.weaken ?_ hflat
  rintro q (hq | ⟨s, ⟨t, ⟨u, hu, h1⟩, h2⟩, h3⟩)
  · exact Or.inl hq
  · exact Or.inr ⟨s, Or.inr ⟨t, Or.inr ⟨u, Or.inr hu, h1⟩, h2⟩, h3⟩

theorem decoded_iff_valid {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((decodedFiber w n).iff (valid w n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact recursive_to_valid (ZFContext.add hZ _) _ _ (add hw _) (decoded_to_recursive _ _ (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact exists_unique (ZFContext.add hZ _) _ _ (add hw _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.StructuralTreeDecode
