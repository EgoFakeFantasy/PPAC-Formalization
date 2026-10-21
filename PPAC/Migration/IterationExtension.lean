import PPAC.Migration.IterationExtensionAlgebra

/-! 全部对象量词下的新鲜后继图扩展保持完整Track及后继域。 -/
namespace PPAC.Migration.IterationExtension
open Source SourceAlgebra SourceLogic OmegaSyntax OmegaStructureSyntax GraphSyntax InsertSyntax IterationSyntax

theorem edge_cases {m} {Γ : Context m} (g f s v j u : Fin m)
    (hl : Derives Γ (GraphInsertSyntax.edgeLaw g f s v)) (hu : Derives Γ (edge g j u)) :
    Derives Γ ((edge f j u).disj ((Formula.equal j s).conj (.equal u v))) := by
  have hi := Derives.allE u (Derives.allE j hl)
  have hr : Derives Γ ((edge g j u).iff ((edge f j u).disj ((Formula.equal j s).conj (.equal u v)))) := by
    simpa only [Formula.instantiate, Formula.rename, Formula.iff, edge_rename, Formula.liftRen,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
  exact .impE (.conjL hr) hu

theorem old_edge {m} {Γ : Context m} (g f s v j u : Fin m)
    (hl : Derives Γ (GraphInsertSyntax.edgeLaw g f s v)) (hu : Derives Γ (edge f j u)) : Derives Γ (edge g j u) := by
  have hi := Derives.allE u (Derives.allE j hl)
  have hr : Derives Γ ((edge g j u).iff ((edge f j u).disj ((Formula.equal j s).conj (.equal u v)))) := by
    simpa only [Formula.instantiate, Formula.rename, Formula.iff, edge_rename, Formula.liftRen,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
  exact .impE (.conjR hr) (.disjL hu)

theorem under_four {m} {Γ : Context m} {q : Formula m} (h : Derives Γ q) :
    Derives (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
      q.raise.raise.raise.raise := .rename Fin.castSucc (.rename Fin.castSucc (.rename Fin.castSucc (.rename Fin.castSucc h)))

theorem next_preserved {m} {Γ : Context m} (g f n s r v : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (functionOn f s)) (hnext : Derives Γ (next f))
    (hn : Derives Γ (transitive n)) (ht : Derives Γ (transitive s))
    (hno : Derives Γ (Formula.mem n n).neg) (hsno : Derives Γ (Formula.mem s s).neg)
    (hsn : Derives Γ (successor s n)) (hr : Derives Γ (edge f n r)) (hv : Derives Γ (unionOf v r))
    (hl : Derives Γ (GraphInsertSyntax.edgeLaw g f s v)) : Derives Γ (next g) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  have he' : Derives Δ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under_four he
  have hf' : Derives Δ (functionOn f.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using under_four hf
  have hnext' : Derives Δ (next f.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, next_rename] using under_four hnext
  have hn' : Derives Δ (transitive n.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, transitive_rename] using under_four hn
  have ht' : Derives Δ (transitive s.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, transitive_rename] using under_four ht
  have hno' : Derives Δ ((Formula.mem n.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc).neg) := by
    simpa only [Formula.raise, Formula.neg, Formula.rename] using under_four hno
  have hsno' : Derives Δ ((Formula.mem s.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc).neg) := by
    simpa only [Formula.raise, Formula.neg, Formula.rename] using under_four hsno
  have hsn' : Derives Δ (successor s.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, successor_rename] using under_four hsn
  have hr' : Derives Δ (edge f.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, edge_rename] using under_four hr
  have hv' : Derives Δ (unionOf v.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using under_four hv
  have hl' : Derives Δ (GraphInsertSyntax.edgeLaw g.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, GraphInsertSyntax.edgeLaw_rename] using under_four hl
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Γq := Context.add (edge g.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+3)))
    (Context.add (edge g.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc) (Context.add (successor (Fin.last (m+1)).castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc) Δ))
  have hI := edge_cases (Γ := Γq) g.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (add (add (add hl' _) _) _) (Derives.hyp (Or.inr (Or.inl rfl)))
  have hK := edge_cases (Γ := Γq) g.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc.castSucc
    (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+3)) (add (add (add hl' _) _) _) (Derives.hyp (Or.inl rfl))
  exact IterationExtensionAlgebra.all_cases f.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))
    (add (add (add he' _) _) _) (add (add (add hf' _) _) _) (add (add (add hnext' _) _) _) (add (add (add hn' _) _) _) (add (add (add ht' _) _) _) (add (add (add hno' _) _) _) (add (add (add hsno' _) _) _) (add (add (add hsn' _) _) _) (add (add (add hr' _) _) _) (add (add (add hv' _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) hI hK

theorem witness_preserved {m} {Γ : Context m} (g e p f n s r v z a : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (track f s z a))
    (hn : Derives Γ (transitive n)) (ht : Derives Γ (transitive s))
    (hno : Derives Γ (Formula.mem n n).neg) (hsno : Derives Γ (Formula.mem s s).neg)
    (hsn : Derives Γ (successor s n)) (hr : Derives Γ (edge f n r)) (hv : Derives Γ (unionOf v r))
    (hw : Derives Γ (GraphInsertSyntax.witness g e p f s s v)) :
    Derives Γ (FiniteIterationSyntax.witness g e s z a) := by
  have hl := Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hw)))
  have hgn := next_preserved g f n s r v he (.conjL hf) (.conjR (.conjR hf)) hn ht hno hsno hsn hr hv hl
  exact .conjI (.conjL (.conjR hw)) (.conjI (.conjL (.conjR (.conjR (.conjR hw))))
    (.conjI (old_edge g f s v z a hl (.conjL (.conjR hf))) hgn))
end PPAC.Migration.IterationExtension
