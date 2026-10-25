import PPAC.Migration.Internal.PacketReaderStateSyntax

/-! Actual reader-state codes exist exactly on raw states, are natural, and uniquely encode all four internal fields. -/
namespace PPAC.Migration.Internal.PacketReaderStateCode
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderStateSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem natural_fields {m} {Γ : Context m} (w l v s a : Fin m) (hi : Derives Γ (PacketReaderStepSyntax.state w l v s a)) :
    Derives Γ (SyntaxForestSyntax.inputs 4 w (fields l v s a)) := by
  change Derives Γ ((Formula.mem l w).conj ((Formula.mem v w).conj ((Formula.mem s w).conj ((Formula.mem a w).conj (.equal w w)))))
  exact .conjI (StructuralListValidity.range w l (.conjL hi)) (.conjI (.conjL (.conjR hi))
    (.conjI (.conjL (.conjR (.conjR hi))) (.conjI (StructuralListValidity.range w a (.conjR (.conjR (.conjR hi)))) (.eqRefl w))))

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w l v s a n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (code w l v s a n)) : Derives Γ (.mem n w) :=
  SyntaxForests.range hZ 4 w (fields l v s a) n hw (.conjR hc)

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w l v s a n r : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (code w l v s a n)) (hr : Derives Γ (code w l v s a r)) : Derives Γ (.equal n r) :=
  SyntaxForests.unique hZ 4 w (fields l v s a) n r hw (.conjR hn) (.conjR hr)

theorem field_eq {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w l v s a x y q c n : Fin m) (i : Fin 4)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (code w l v s a n)) (hr : Derives Γ (code w x y q c n)) :
    Derives Γ (.equal (fields l v s a i) (fields x y q c i)) :=
  SyntaxForestInjective.input_eq hZ 4 w (fields l v s a) (fields x y q c) n i hw (.conjR hn) (.conjR hr)

theorem fields_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w l v s a x y q c n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (code w l v s a n)) (hr : Derives Γ (code w x y q c n)) :
    Derives Γ (PacketReaderStep.same l v s a x y q c) :=
  .conjI (field_eq hZ w l v s a x y q c n 0 hw hn hr) (.conjI (field_eq hZ w l v s a x y q c n 1 hw hn hr)
    (.conjI (field_eq hZ w l v s a x y q c n 2 hw hn hr) (field_eq hZ w l v s a x y q c n 3 hw hn hr)))

theorem exists_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w l v s a : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (PacketReaderStepSyntax.state w l v s a)) : Derives Γ (existsCode w l v s a) := by
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxForestSyntax.forest 4 w.castSucc (fun i => (fields l v s a i).castSucc) (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (SyntaxForests.exists_forest hZ 4 w (fields l v s a) hw (natural_fields w l v s a hi))
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hi1 := of_eq (PacketReaderStepSyntax.state_rename w l v s a Fin.castSucc) (under hi R)
  have hc : Derives Δ (code w.castSucc l.castSucc v.castSucc s.castSucc a.castSucc (Fin.last m)) :=
    .conjI hi1 (of_eq (by rw [fields_map]) (.conjR hR))
  have hout : Derives Δ (existsCode w.castSucc l.castSucc v.castSucc s.castSucc a.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate,Formula.rename,code_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI (.conjL hR) hc)
  simpa only [Formula.raise,existsCode_rename] using hout

theorem exists_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w l v s a : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ ((existsCode w l v s a).iff (PacketReaderStepSyntax.state w l v s a)) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := existsCode w l v s a
    let R := (Formula.mem (Fin.last m) w.castSucc).conj (code w.castSucc l.castSucc v.castSucc s.castSucc a.castSucc (Fin.last m))
    let Δ := Context.add R (Context.image Formula.raise (Context.add H Γ))
    apply Derives.exE (p := R) (.hyp (Or.inl rfl))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    exact of_eq (by simp only [Formula.raise,PacketReaderStepSyntax.state_rename]) (.conjL (.conjR hR))
  · apply Derives.impI
    exact exists_code (ZFContext.add hZ _) w l v s a (add hw _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.PacketReaderStateCode
