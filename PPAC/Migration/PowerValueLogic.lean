import PPAC.Migration.PowerValueSyntax

/-! 有效完整历史图的每个输入都有实际唯一的输出幂集，无宿主数据选择。 -/
namespace PPAC.Migration.PowerValueLogic
open Source SourceAlgebra SourceLogic GraphSyntax PowerSetSyntax PowerValueSyntax

theorem exists_value {m} {Γ : Context m} (h a b : Fin m)
    (hp : Derives Γ (Source.SetLanguage.powerSet.rename Fin.elim0))
    (hf : Derives Γ (functionOn h a)) (hb : Derives Γ (.mem b a)) : Derives Γ (PowerValueSyntax.valueExists h b) := by
  have hex := GraphProperties.output_exists h a b hf hb
  let V := edge h.castSucc b.castSucc (Fin.last m)
  let Γv := Context.add V (Context.image Formula.raise Γ)
  change Derives Γ (.ex V) at hex
  apply Derives.exE (p := V) hex
  have hpV : Derives Γv (Source.SetLanguage.powerSet.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hp V
  have hV : Derives Γv V := .hyp (Or.inl rfl)
  have hw := power_instance (Fin.last m) hpV
  let W := powerOf (Fin.last (m+1)) (Fin.last m).castSucc
  let Γw := Context.add W (Context.image Formula.raise Γv)
  change Derives Γv (.ex W) at hw
  apply Derives.exE (p := W) hw
  have hVW : Derives Γw (edge h.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [Formula.raise, V, edge_rename] using under hV W
  have hW : Derives Γw W := .hyp (Or.inl rfl)
  have hv := intro_value h.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hVW hW
  have hout : Derives Γw (PowerValueSyntax.valueExists h.castSucc.castSucc b.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    simpa only [Formula.instantiate, value_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hv
  simpa only [Formula.raise, PowerValueSyntax.valueExists_rename] using hout

theorem unique_values {m} {Γ : Context m} (h a b w z : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (functionOn h a)) (hw : Derives Γ (value h b w)) (hz : Derives Γ (value h b z)) :
    Derives Γ (.equal w z) := by
  let V := (edge h.castSucc b.castSucc (Fin.last m)).conj (powerOf w.castSucc (Fin.last m))
  let Γv := Context.add V (Context.image Formula.raise Γ)
  change Derives Γ (.ex V) at hw
  apply Derives.exE (p := V) hw
  have heV : Derives Γv (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he V
  have hfV : Derives Γv (functionOn h.castSucc a.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using under hf V
  have hzV : Derives Γv (value h.castSucc b.castSucc z.castSucc) := by
    simpa only [Formula.raise, value_rename] using under hz V
  have hV : Derives Γv V := .hyp (Or.inl rfl)
  let U := (edge h.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1))).conj
    (powerOf z.castSucc.castSucc (Fin.last (m+1)))
  let Ξ := Context.add U (Context.image Formula.raise Γv)
  change Derives Γv (.ex U) at hzV
  apply Derives.exE (p := U) hzV
  have heU : Derives Ξ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under heV U
  have hfU : Derives Ξ (functionOn h.castSucc.castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using under hfV U
  have hVU : Derives Ξ ((edge h.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc).conj
      (powerOf w.castSucc.castSucc (Fin.last m).castSucc)) := by
    simpa only [Formula.raise, V, Formula.rename, edge_rename, powerOf_rename] using under hV U
  have hU : Derives Ξ U := .hyp (Or.inl rfl)
  have hvalues := GraphProperties.single_valued h.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) heU hfU (.conjL hVU) (.conjL hU)
  have hzPower := PowerSetLogic.subst_base z.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc (eq_symm hvalues) (.conjR hU)
  exact PowerSetLogic.unique w.castSucc.castSucc z.castSucc.castSucc (Fin.last m).castSucc heU (.conjR hVU) hzPower

theorem unique_formula {m} {Γ : Context m} (h a b w : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (functionOn h a)) (hw : Derives Γ (value h b w)) : Derives Γ (uniqueValue h b w) := by
  apply Derives.allI
  have he' : Derives (Context.image Formula.raise Γ) (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc he
  have hf' : Derives (Context.image Formula.raise Γ) (functionOn h.castSucc a.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using Derives.rename Fin.castSucc hf
  have hw' : Derives (Context.image Formula.raise Γ) (value h.castSucc b.castSucc w.castSucc) := by
    simpa only [Formula.raise, value_rename] using Derives.rename Fin.castSucc hw
  apply Derives.impI
  exact unique_values h.castSucc a.castSucc b.castSucc (Fin.last m) w.castSucc (add he' _) (add hf' _) (.hyp (Or.inl rfl)) (add hw' _)

theorem fiber_at {m} {Γ : Context m} (h a b : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hp : Derives Γ (Source.SetLanguage.powerSet.rename Fin.elim0))
    (hf : Derives Γ (functionOn h a)) (hb : Derives Γ (.mem b a)) : Derives Γ (fiber h b) := by
  have hex := exists_value h a b hp hf hb
  let W := value h.castSucc b.castSucc (Fin.last m)
  let Ξ := Context.add W (Context.image Formula.raise Γ)
  change Derives Γ (.ex W) at hex
  apply Derives.exE (p := W) hex
  have heW : Derives Ξ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he W
  have hfW : Derives Ξ (functionOn h.castSucc a.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using under hf W
  have hW : Derives Ξ W := .hyp (Or.inl rfl)
  have hu := unique_formula h.castSucc a.castSucc b.castSucc (Fin.last m) heW hfW hW
  have hout : Derives Ξ (fiber h.castSucc b.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, value_rename, uniqueValue_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hW hu
  simpa only [Formula.raise, fiber_rename] using hout
end PPAC.Migration.PowerValueLogic
