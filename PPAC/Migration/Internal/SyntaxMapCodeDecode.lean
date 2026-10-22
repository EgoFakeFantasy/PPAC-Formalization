import PPAC.Migration.Internal.SyntaxMapCodeExistence

/-! 任意内部MapCode实际唯一解码回完整原图，保留原长度、域和目标范围。 -/
namespace PPAC.Migration.Internal.SyntaxMapCodeDecode
open Source SourceAlgebra SourceLogic SyntaxMapCodeSyntax

theorem natural {m} {Γ : Context m} (w a c k : Fin m) (hc : Derives Γ (mapCode w a c k)) : Derives Γ (.mem k w) := by
  let R := encoded w.castSucc (Fin.last m) a.castSucc c.castSucc k.castSucc
  let Δ := Context.add R (Context.image Formula.raise Γ)
  change Derives Γ (.ex R) at hc
  apply Derives.exE hc
  exact SyntaxMapCode.code_natural _ _ _ _ _ (.hyp (Or.inl rfl))

theorem contexts {m} {Γ : Context m} (w a c k : Fin m) (hc : Derives Γ (mapCode w a c k)) :
    Derives Γ (SyntaxTermSyntax.contexts w a c) := by
  let R := encoded w.castSucc (Fin.last m) a.castSucc c.castSucc k.castSucc
  let Δ := Context.add R (Context.image Formula.raise Γ)
  change Derives Γ (.ex R) at hc
  apply Derives.exE hc
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have ho := Derives.conjL (.conjR hR)
  simpa only [Formula.raise, SyntaxTermSyntax.contexts_rename] using ho

theorem valid {m} {Γ : Context m} (w a c k : Fin m) (hc : Derives Γ (mapCode w a c k)) :
    Derives Γ (StructuralListTraceSyntax.valid w k) := by
  let R := encoded w.castSucc (Fin.last m) a.castSucc c.castSucc k.castSucc
  let Δ := Context.add R (Context.image Formula.raise Γ)
  change Derives Γ (.ex R) at hc
  apply Derives.exE hc
  have ho := SyntaxMapCode.code_valid w.castSucc (Fin.last m) a.castSucc c.castSucc k.castSucc (Derives.hyp (Or.inl rfl) : Derives Δ R)
  simpa only [Formula.raise, StructuralListTraceSyntax.valid_rename] using ho

theorem actual_graph_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c k : Fin m)
    (hc : Derives Γ (mapCode w a c k)) : Derives Γ (graphFiber w a c k) := by
  let R := encoded w.castSucc (Fin.last m) a.castSucc c.castSucc k.castSucc
  let Ξ := Context.add R (Context.image Formula.raise Γ)
  change Derives Γ (.ex R) at hc
  apply Derives.exE hc
  have hR : Derives Ξ R := .hyp (Or.inl rfl)
  have hu : Derives Ξ (.all ((encoded w.castSucc.castSucc (Fin.last (m+1)) a.castSucc.castSucc c.castSucc.castSucc k.castSucc.castSucc).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let S := encoded w.castSucc.castSucc (Fin.last (m+1)) a.castSucc.castSucc c.castSucc.castSucc k.castSucc.castSucc
    let Δ := Context.add S (Context.image Formula.raise Ξ)
    have hr2 : Derives Δ (encoded w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc c.castSucc.castSucc k.castSucc.castSucc) := by
      simpa only [R, Formula.raise, encoded_rename] using under hR S
    exact SyntaxMapCode.unique_graph (ZFContext.under (ZFContext.under hZ R) S) _ _ _ _ _ _ (.hyp (Or.inl rfl)) hr2
  have ho : Derives Ξ (graphFiber w.castSucc a.castSucc c.castSucc k.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, encoded_rename, Formula.liftRen,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hR hu
  simpa only [Formula.raise, graphFiber_rename] using ho

theorem code_of_fiber {m} {Γ : Context m} (w a c k : Fin m) (hc : Derives Γ (graphFiber w a c k)) :
    Derives Γ (mapCode w a c k) := by
  let R := (encoded w.castSucc (Fin.last m) a.castSucc c.castSucc k.castSucc).conj
    (.all ((encoded w.castSucc.castSucc (Fin.last (m+1)) a.castSucc.castSucc c.castSucc.castSucc k.castSucc.castSucc).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc)))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  change Derives Γ (.ex R) at hc
  apply Derives.exE hc
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have ho := intro_code _ _ _ _ _ (.conjL hR)
  simpa only [Formula.raise, mapCode_rename] using ho

theorem fiber_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c k : Fin m) :
    Derives Γ ((mapCode w a c k).iff (graphFiber w a c k)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact actual_graph_fiber (ZFContext.add hZ _) w a c k (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact code_of_fiber w a c k (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.SyntaxMapCodeDecode
