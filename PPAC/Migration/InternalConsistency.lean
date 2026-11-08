import PPAC.Migration.OriginalAxiomTyping

/-! The concrete final Con contract, using the unchanged original structural
axiom test and six-rule root relation. All proof and formula witnesses are
internal objects. The closing certificate consumes the explicitly stated
all-internal contradiction reduction; it does NOT prove that reduction or Con.
No new checker, satisfaction predicate or proof kernel is introduced. -/
namespace PPAC.Migration.InternalConsistency
open Internal Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

/-- A closed proof root with the exact internally quoted native falsum. -/
def contradiction {m} (target : Bool) (w p : Fin m) : Formula m := .ex
  ((PureQuotationSyntax.formula (.falsum : PureSyntaxQuotation.Fm [] [])
    w.castSucc (Fin.last m)).conj
      (ProofTreeEntrySyntax.root (OriginalAxiomCodeTest.test target)
        w.castSucc p.castSucc (Fin.last m)))

def inconsistentAt {m} (target : Bool) (w : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj
    (contradiction target w.castSucc (Fin.last m)))

def inconsistent {m} (target : Bool) : Formula m := .ex
  ((omega (Fin.last m)).conj (inconsistentAt target (Fin.last m)))

def con {m} (target : Bool) : Formula m := (inconsistent target).neg

private def pointReduction (w p : Fin 2) : Formula 2 :=
  (omega w).imp ((Formula.mem p w).imp
    ((contradiction true w p).imp (inconsistentAt false w)))

/-- Every INTERNAL U contradiction code has a ZF contradiction code in the
same omega. This sentence remains an outstanding mathematical obligation. -/
def reduction : Source.Sentence := (pointReduction 0 1).close

def nativeCon (target : Bool) := Translation.sentence (con (m := 0) target)

def goal := YesMetaZFC.Logic.FirstOrder.Formula.imp (nativeCon false) (nativeCon true)

private theorem contradiction_rename {m n} (target : Bool) (w p : Fin m) (r : Fin m → Fin n) :
    (contradiction target w p).rename r = contradiction target (r w) (r p) := by
  simp only [contradiction, Formula.rename, PureQuotationSyntax.formula_rename,
    ProofTreeEntryFacts.root_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem inconsistentAt_rename {m n} (target : Bool) (w : Fin m) (r : Fin m → Fin n) :
    (inconsistentAt target w).rename r = inconsistentAt target (r w) := by
  simp only [inconsistentAt, Formula.rename, contradiction_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem inconsistent_rename {m n} (target : Bool) (r : Fin m → Fin n) :
    (inconsistent (m := m) target).rename r = inconsistent (m := n) target := by
  simp only [inconsistent, Formula.rename, omega_rename, inconsistentAt_rename,
    Formula.liftRen, Fin.lastCases_last]

private theorem pointReduction_rename {m} (w p : Fin 2) (r : Fin 2 → Fin m) :
    (pointReduction w p).rename r = (omega (r w)).imp ((Formula.mem (r p) (r w)).imp
      ((contradiction true (r w) (r p)).imp (inconsistentAt false (r w)))) := by
  simp only [pointReduction, Formula.rename, omega_rename, contradiction_rename, inconsistentAt_rename]

private theorem reduce_at {m} {Γ : Context m} (w p : Fin m)
    (hr : Derives Γ (reduction.rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hp : Derives Γ (.mem p w))
    (hc : Derives Γ (contradiction true w p)) : Derives Γ (inconsistentAt false w) := by
  have h := specialize_close (pointReduction 0 1) (SetLanguage.args2 w p) hr
  have h0 := of_eq (by simpa only [SetLanguage.args2, Fin.cases_zero, Fin.cases_succ]
    using pointReduction_rename 0 1 (SetLanguage.args2 w p)) h
  exact .impE (.impE (.impE h0 hw) hp) hc

private theorem inconsistent_transfer {m} {Γ : Context m}
    (hr : Derives Γ (reduction.rename Fin.elim0)) (hu : Derives Γ (inconsistent true)) :
    Derives Γ (inconsistent false) := by
  let B := (omega (Fin.last m)).conj (inconsistentAt true (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hu
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hr1 := of_eq (closed_rename reduction Fin.castSucc) (under hr B)
  let C := (Formula.mem (Fin.last (m+1)) (Fin.last m).castSucc).conj
    (contradiction true (Fin.last m).castSucc (Fin.last (m+1)))
  let Ξ := Context.add C (Context.image Formula.raise Δ)
  apply Derives.exE (p := C) (.conjR hB)
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have hw2 := of_eq (omega_rename (Fin.last m) Fin.castSucc) (under (.conjL hB) C)
  have hr2 := of_eq (closed_rename reduction Fin.castSucc) (under hr1 C)
  have hz := reduce_at (Fin.last m).castSucc (Fin.last (m+1)) hr2 hw2 (.conjL hC) (.conjR hC)
  have ho : Derives Ξ (inconsistent false) := by
    apply Derives.exI (Fin.last m).castSucc
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, omega_rename,
      inconsistentAt_rename, Fin.lastCases_last]) (.conjI hw2 hz)
  exact of_eq (by simp only [Formula.raise, inconsistent_rename]) ho

private theorem source_closing : Derives (Source.SetLanguage.ZF.at 0)
    (.imp reduction (.imp (con (m := 0) false) (con true))) := by
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  have hzero : (Fin.elim0 : Fin 0 → Fin 0) = id := by
    funext i
    exact Fin.elim0 i
  let Δ := Context.add (inconsistent (m := 0) true)
    (Context.add (con false) (Context.add reduction (Source.SetLanguage.ZF.at 0)))
  have hred : Derives Δ reduction := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have hr : Derives Δ (reduction.rename Fin.elim0) :=
    of_eq (by rw [hzero, Reverse.source_rename_id]) hred
  exact .impE (.hyp (Or.inr (Or.inl rfl)))
    (inconsistent_transfer hr (.hyp (Or.inl rfl)))

/-- The final logical closing gate, not a proof of `goal`. -/
theorem closing_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (.imp (Translation.sentence reduction) goal) :=
  ZFReplay.replay (TheoryTransport.sentence source_closing)

end PPAC.Migration.InternalConsistency
