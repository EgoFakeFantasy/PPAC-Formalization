import PPAC.Migration.Internal.StructuralListLengthBasic

/-! 精确末Cons行和已知尾码的真实前驱边；不丢弃固定前驱长度。 -/
namespace PPAC.Migration.Internal.StructuralListTerminal
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SequenceSyntax StructuralListSyntax StructuralListTraceSyntax StructuralListTraceOrder
open StructuralListTraceProperties
attribute [local irreducible] NaturalRecursionSyntax.matrix

def terminal {m} (w f p n : Fin m) : Formula m := .ex
  ((edge f.castSucc p.castSucc (Fin.last m)).conj (step w.castSucc (Fin.last m) n.castSucc))
theorem terminal_rename {m k} (w f p n : Fin m) (r : Fin m → Fin k) :
    (terminal w f p n).rename r = terminal (r w) (r f) (r p) (r n) := by
  simp only [terminal, Formula.rename, edge_rename, step_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem intro_terminal {m} {Γ : Context m} (w f p n a : Fin m) (ha : Derives Γ (edge f p a)) (hs : Derives Γ (step w a n)) : Derives Γ (terminal w f p n) := by
  apply Derives.exI a
  simp only [Formula.instantiate, Formula.rename, edge_rename, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI ha hs

theorem terminal_link {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e l d f n p : Fin m)
    (hs : Derives Γ (successor l p)) (ht : Derives Γ (trace w z e l d f n)) : Derives Γ (terminal w f p n) := by
  have hr := StructuralListTraceSyntax.links_at _ _ _ _ (links_at_trace _ _ _ _ _ _ _ ht) (InsertLogic.new_member _ _ _ hs)
  let R := rowWitness w f p
  let Δ := Context.add R (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  apply eliminate_row w f p _ hr
  have hZ3 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.rename (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) Fin.castSucc) R
  have hs3 : Derives Δ (successor l.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using GraphInsertElimination.under_three hs R
  have ht3 : Derives Δ (trace w.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc l.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, trace_rename] using GraphInsertElimination.under_three ht R
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hjl := OmegaUniversal.successor_unique _ _ _ (ZFContext.arithmetic hZ3).base.extensionality (.conjL hR) hs3
  have hedge := edge_input_subst _ _ _ _ hjl (.conjL (.conjR (.conjR hR)))
  have hbn := GraphProperties.single_valued _ _ _ _ _ (ZFContext.arithmetic hZ3).base.extensionality
    (.conjL (sequence_at _ _ _ _ _ _ _ ht3)) hedge (last_at _ _ _ _ _ _ _ ht3)
  have hstep := step_output_subst _ _ _ _ hbn (.conjR (.conjR (.conjR hR)))
  have hout := intro_terminal _ _ _ _ _ (.conjL (.conjR hR)) hstep
  simpa only [Formula.raise, terminal_rename] using hout

theorem step_nil_disjoint {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (nilCode w n)) (hs : Derives Γ (step w a n)) : Derives Γ .bot := by
  let H := (Formula.mem (Fin.last m) w.castSucc).conj (consCode w.castSucc (Fin.last m) a.castSucc n.castSucc)
  let Δ := Context.add H (Context.image Formula.raise Γ)
  change Derives Γ (.ex H) at hs
  apply Derives.exE (p := H) hs
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ H
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw H
  have hn1 : Derives Δ (nilCode w.castSucc n.castSucc) := by simpa only [Formula.raise, nilCode_rename] using under hn H
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  exact StructuralConsUnique.disjoint hZ1 _ _ _ _ hw1 hn1 (.conjR hH)

theorem no_nil_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e l d f n p : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (successor l p)) (ht : Derives Γ (trace w z e l d f n))
    (hn : Derives Γ (nilCode w n)) : Derives Γ .bot := by
  have ha := terminal_link hZ _ _ _ _ _ _ _ _ hs ht
  let A := (edge f.castSucc p.castSucc (Fin.last m)).conj (step w.castSucc (Fin.last m) n.castSucc)
  let Δ := Context.add A (Context.image Formula.raise Γ)
  change Derives Γ (.ex A) at ha
  apply Derives.exE (p := A) ha
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ A
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw A
  have hn1 : Derives Δ (nilCode w.castSucc n.castSucc) := by simpa only [Formula.raise, nilCode_rename] using under hn A
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  exact step_nil_disjoint hZ1 _ _ _ hw1 hn1 (.conjR hA)

theorem known_tail_edge {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e l d f n p h t : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hs : Derives Γ (successor l p)) (hf : Derives Γ (trace w z e l d f n))
    (hc : Derives Γ (consCode w h t n)) : Derives Γ (edge f p t) := by
  have ha := terminal_link hZ _ _ _ _ _ _ _ _ hs hf
  let A := (edge f.castSucc p.castSucc (Fin.last m)).conj (step w.castSucc (Fin.last m) n.castSucc)
  let Ξ := Context.add A (Context.image Formula.raise Γ)
  change Derives Γ (.ex A) at ha
  apply Derives.exE (p := A) ha
  have hA : Derives Ξ A := .hyp (Or.inl rfl)
  have hf1 : Derives Ξ (trace w.castSucc z.castSucc e.castSucc l.castSucc d.castSucc f.castSucc n.castSucc) := by simpa only [Formula.raise, trace_rename] using under hf A
  have haW := Derives.impE (SequenceSyntax.bounded_at _ _ _ _ (.conjR (sequence_at _ _ _ _ _ _ _ hf1))) (.conjL hA)
  let H := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (consCode w.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc n.castSucc.castSucc)
  let Δ := Context.add H (Context.image Formula.raise Ξ)
  have hhead : Derives Ξ (.ex H) := .conjR hA
  apply Derives.exE (p := H) hhead
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ A) H
  have lift {q : Formula m} (hq : Derives Γ q) : Derives Δ q.raise.raise := under (under hq A) H
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hc2 : Derives Δ (consCode w.castSucc.castSucc h.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, consCode_rename] using lift hc
  have hedge2 : Derives Δ (edge f.castSucc.castSucc p.castSucc.castSucc (Fin.last m).castSucc) := by simpa only [Formula.raise, edge_rename] using under (Derives.conjL hA) H
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have heq := StructuralConsUnique.injective hZ2 _ _ _ _ _ _ hw2 (.conjL hH) (under haW H) (lift hh) (lift ht) (.conjR hH) hc2
  have hout := GraphPointwiseSyntax.edge_subst_output _ _ _ _ (.conjR heq) hedge2
  simpa only [Formula.raise, edge_rename] using hout
end PPAC.Migration.Internal.StructuralListTerminal
