import PPAC.Migration.ForcingConditionRebind
import PPAC.Migration.ForcingExistGuardsCode
import PPAC.Migration.Internal.FormulaCodeConstructors

/-! The density hypothesis of the pinned OpenAI theorem
OAI.PartitionConsistency.ForcingQuotient.AtomicData.force_of_dense.
The witness body must live under both condition binders. Its compiled formula
code and scopes are internal naturals throughout. -/
namespace PPAC.Migration.ForcingDensityCode
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open SyntaxMixedFormulaJudgmentSyntax (substituted substituted_rename)

set_option maxRecDepth 16384

private theorem with_witness {m} {Γ : Context m} {P : Formula (m+1)} {out : Formula m}
    (hZ : ZFContext.Evidence Γ) (he : Derives Γ (.ex P))
    (use :
      let Δ := Context.add P (Context.image Formula.raise Γ)
      ZFContext.Evidence Δ →
      (∀ {p : Formula m}, Derives Γ p → Derives Δ (p.rename Fin.castSucc)) →
      Derives Δ P → Derives Δ (out.rename Fin.castSucc)) :
    Derives Γ out :=
  Derives.exE he (use (ZFContext.under hZ P) (fun h => under h P) (.hyp (Or.inl rfl)))

private def weakenData {m} (w a A f N W : Fin m) (v : Fin 3 → Fin m) : Formula m :=
  (SyntaxVariableTableSyntax.shifted true w a A f (v 0)).conj
    ((SyntaxMixedImageCodeSyntax.encoded w (v 0) a A f (v 1)).conj
      ((ForcingAtomicCode.identityImages w A f (v 2)).conj
        (substituted w (v 1) (v 2) a f A f N W)))

private theorem weakenData_rename {m l} (w a A f N W : Fin m) (v : Fin 3 → Fin m)
    (ρ : Fin m → Fin l) :
    (weakenData w a A f N W v).rename ρ =
      weakenData (ρ w) (ρ a) (ρ A) (ρ f) (ρ N) (ρ W) (fun i => ρ (v i)) := by
  simp only [weakenData, Formula.rename, SyntaxVariableTableSyntax.shifted_rename,
    SyntaxMixedImageCodeSyntax.encoded_rename, ForcingAtomicCode.identityImages_rename, substituted_rename]

private def weakenBody {m} (w a A f N W : Fin m) : Formula (m+3) :=
  weakenData (old 3 w) (old 3 a) (old 3 A) (old 3 f) (old 3 N) (old 3 W) (slot 3)

/-- Insert the outer condition binder and keep the free condition slot. -/
def weakened {m} (w a A f N W : Fin m) : Formula m := existsMany 3 (weakenBody w a A f N W)

theorem weakened_rename {m l} (w a A f N W : Fin m) (ρ : Fin m → Fin l) :
    (weakened w a A f N W).rename ρ = weakened (ρ w) (ρ a) (ρ A) (ρ f) (ρ N) (ρ W) := by
  simp only [weakened, weakenBody, existsMany_rename, weakenData_rename, lift_old, lift_slot]

private theorem intro_weakened {m} {Γ : Context m} (w a A f N W : Fin m)
    (v : Fin 3 → Fin m) (h : Derives Γ (weakenData w a A f N W v)) :
    Derives Γ (weakened w a A f N W) := by
  apply HornBinderRules.intro_many 3 (weakenBody w a A f N W) v
  exact of_eq (by simp only [weakenBody, weakenData_rename, assign_old, assign_slot]) h

theorem weakened_type {m} {Γ : Context m} (w a A f N W : Fin m)
    (h : Derives Γ (weakened w a A f N W)) : Derives Γ (formulaCode w W A f) := by
  let P := weakenBody w a A f N W
  apply HornBinderRules.eliminate_many 3 P _ h
  have hP : Derives (Context.add P (raisedContext 3 Γ)) P := .hyp (Or.inl rfl)
  exact of_eq (formulaCode_rename w W A f (old 3)).symm
    (SyntaxMixedFormulaJudgment.target_type (old 3 w) (slot 3 1) (slot 3 2)
      (old 3 a) (old 3 f) (old 3 A) (old 3 f) (old 3 N) (old 3 W) (.conjR (.conjR (.conjR hP))))

private def existsWeakened {m} (w a A f N : Fin m) : Formula m :=
  .ex (weakened w.castSucc a.castSucc A.castSucc f.castSucc N.castSucc (Fin.last m))

private theorem existsWeakened_rename {m l} (w a A f N : Fin m) (ρ : Fin m → Fin l) :
    (existsWeakened w a A f N).rename ρ = existsWeakened (ρ w) (ρ a) (ρ A) (ρ f) (ρ N) := by
  simp only [existsWeakened, Formula.rename, weakened_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem weaken_with_lists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A f N F L S : Fin m) (hw : Derives Γ (omega w)) (hN : Derives Γ (formulaCode w N a f))
    (hF : Derives Γ (SyntaxVariableTableSyntax.shifted true w a A f F))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.encoded w F a A f L))
    (hS : Derives Γ (ForcingAtomicCode.identityImages w A f S)) :
    Derives Γ (existsWeakened w a A f N) := by
  have hi : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w L S a f A f N) :=
    .conjI hN (.conjI (SyntaxMixedImageCodeFields.term_list w F a A f L hL)
      (ForcingAtomicCode.identityImages_typed w A f S hS))
  let P := substituted w.castSucc L.castSucc S.castSucc a.castSucc f.castSucc
    A.castSucc f.castSucc N.castSucc (Fin.last m)
  apply with_witness (P := P) hZ (SyntaxMixedFormulaOutputInduction.actual_exists hZ w L S a f A f N hw hi)
  intro Δ _ lift hP
  rw [existsWeakened_rename]
  apply Derives.exI (Fin.last m)
  simp only [Formula.instantiate, weakened_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  let v : Fin 3 → Fin (m+1) := Fin.cases F.castSucc (SetLanguage.args2 L.castSucc S.castSucc)
  apply intro_weakened _ _ _ _ _ _ v
  exact .conjI (of_eq (SyntaxVariableTableSyntax.shifted_rename true w a A f F Fin.castSucc) (lift hF))
    (.conjI (of_eq (SyntaxMixedImageCodeSyntax.encoded_rename w F a A f L Fin.castSucc) (lift hL))
      (.conjI (of_eq (ForcingAtomicCode.identityImages_rename w A f S Fin.castSucc) (lift hS)) hP))

private theorem weaken_with_table {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A f N F : Fin m) (hw : Derives Γ (omega w)) (hA : Derives Γ (.mem A w))
    (hf : Derives Γ (.mem f w)) (hN : Derives Γ (formulaCode w N a f))
    (hF : Derives Γ (SyntaxVariableTableSyntax.shifted true w a A f F)) :
    Derives Γ (existsWeakened w a A f N) := by
  have hm := SyntaxVariableTableUnique.shifted_type true w a A f F hF
  let P := SyntaxMixedImageCodeSyntax.encoded w.castSucc F.castSucc a.castSucc A.castSucc f.castSucc (Fin.last m)
  apply with_witness (P := P) hZ (SyntaxMixedImageCodeExistence.exists_code hZ w F a A f hw hm)
  intro Δ hZ1 lift hL
  rw [existsWeakened_rename]
  have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
  have hN1 := of_eq (formulaCode_rename w N a f Fin.castSucc) (lift hN)
  have hF1 := of_eq (SyntaxVariableTableSyntax.shifted_rename true w a A f F Fin.castSucc) (lift hF)
  let Q := ForcingAtomicCode.identityImages w.castSucc.castSucc A.castSucc.castSucc f.castSucc.castSucc (Fin.last (m+1))
  apply with_witness (P := Q) hZ1
    (ForcingAtomicCode.identityImages_exists hZ1 w.castSucc A.castSucc f.castSucc hw1 (lift hA) (lift hf))
  intro Δ hZ2 lift1 hS
  rw [existsWeakened_rename]
  exact weaken_with_lists hZ2 w.castSucc.castSucc a.castSucc.castSucc A.castSucc.castSucc f.castSucc.castSucc
    N.castSucc.castSucc F.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    (of_eq (omega_rename _ _) (lift1 hw1)) (of_eq (formulaCode_rename _ _ _ _ _) (lift1 hN1))
    (of_eq (SyntaxVariableTableSyntax.shifted_rename true _ _ _ _ _ _) (lift1 hF1))
    (of_eq (SyntaxMixedImageCodeSyntax.encoded_rename _ _ _ _ _ _ _) (lift1 hL)) hS

private theorem weaken_total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A f N : Fin m) (hw : Derives Γ (omega w)) (hs : Derives Γ (successor A a))
    (hN : Derives Γ (formulaCode w N a f)) : Derives Γ (existsWeakened w a A f N) := by
  have hsco := Derives.conjR (FormulaCodeProperties.guards w N a f hN)
  have ha := Derives.conjL hsco
  have hf := Derives.conjR hsco
  have hA := OmegaStructureAlgebra.successor_member w A a (ZFContext.arithmetic hZ).base.extensionality hw ha hs
  let P := SyntaxVariableTableSyntax.shifted true w.castSucc a.castSucc A.castSucc f.castSucc (Fin.last m)
  apply with_witness (P := P) hZ
    (SyntaxVariableTableExistence.shifted_exists hZ true w a A f hw (.conjI hA hf) ha hs)
  intro Δ hZ1 lift hF
  rw [existsWeakened_rename]
  exact weaken_with_table hZ1 w.castSucc a.castSucc A.castSucc f.castSucc N.castSucc (Fin.last m)
    (of_eq (omega_rename _ _) (lift hw)) (lift hA) (lift hf)
    (of_eq (formulaCode_rename _ _ _ _ _) (lift hN)) hF

/-- Under q then r, the old bounds have shifted twice and only free slot j is
replaced by bound 0, the new witness condition r. -/
def rebound {m} (w a A B f j N Q : Fin m) : Formula m := .ex
  ((weakened w.castSucc a.castSucc A.castSucc f.castSucc N.castSucc (Fin.last m)).conj
    (ForcingConditionRebind.compiled w.castSucc A.castSucc f.castSucc B.castSucc j.castSucc
      (Fin.last m) Q.castSucc))

theorem rebound_rename {m l} (w a A B f j N Q : Fin m) (ρ : Fin m → Fin l) :
    (rebound w a A B f j N Q).rename ρ = rebound (ρ w) (ρ a) (ρ A) (ρ B) (ρ f) (ρ j) (ρ N) (ρ Q) := by
  simp only [rebound, Formula.rename, weakened_rename, ForcingConditionRebind.compiled_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

def existsRebound {m} (w a A B f j N : Fin m) : Formula m :=
  .ex (rebound w.castSucc a.castSucc A.castSucc B.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m))

theorem existsRebound_rename {m l} (w a A B f j N : Fin m) (ρ : Fin m → Fin l) :
    (existsRebound w a A B f j N).rename ρ = existsRebound (ρ w) (ρ a) (ρ A) (ρ B) (ρ f) (ρ j) (ρ N) := by
  simp only [existsRebound, Formula.rename, rebound_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem rebound_total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a A B f j N : Fin m)
    (hw : Derives Γ (omega w)) (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A))
    (hN : Derives Γ (formulaCode w N a f)) : Derives Γ (existsRebound w a A B f j N) := by
  let P := weakened w.castSucc a.castSucc A.castSucc f.castSucc N.castSucc (Fin.last m)
  apply with_witness (P := P) hZ (weaken_total hZ w a A f N hw hA hN)
  intro Δ hZ1 lift hW
  rw [existsRebound_rename]
  let Q := ForcingConditionRebind.compiled w.castSucc.castSucc A.castSucc.castSucc f.castSucc.castSucc
    B.castSucc.castSucc j.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  apply with_witness (P := Q) hZ1
    (ForcingConditionRebind.total hZ1 w.castSucc A.castSucc f.castSucc B.castSucc j.castSucc (Fin.last m)
      (of_eq (omega_rename _ _) (lift hw)) (of_eq (successor_rename _ _ _) (lift hB))
      (weakened_type w.castSucc a.castSucc A.castSucc f.castSucc N.castSucc (Fin.last m) hW))
  intro Δ _ lift1 hQ
  rw [existsRebound_rename]
  apply Derives.exI (Fin.last (m+1))
  simp only [Formula.instantiate, rebound_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  apply Derives.exI (Fin.last m).castSucc
  simp only [Formula.instantiate, Formula.rename, weakened_rename, ForcingConditionRebind.compiled_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI (of_eq (weakened_rename _ _ _ _ _ _ _) (lift1 hW)) hQ

theorem rebound_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B f j N Q : Fin m) (h : Derives Γ (rebound w a A B f j N Q)) :
    Derives Γ (formulaCode w Q B f) := by
  unfold rebound at h
  apply with_witness hZ h
  intro Δ _ _ hp
  rw [formulaCode_rename]
  exact ForcingConditionRebind.compiled_type w.castSucc A.castSucc f.castSucc B.castSucc j.castSucc
    (Fin.last m) Q.castSucc (.conjR hp)


open FormulaCodeConstructSyntax (typedAt typedAt_rename typedFiber)

/-- Exact constructor trace for
ALL q (q in P -> R(q,p) -> EX r (r in P AND R(r,q) AND body)). -/
def shellData {m} (w a A B f qM qO rM rO body D : Fin m) (v : Fin 5 → Fin m) : Formula m :=
  (typedAt 2 5 w (SyntaxAtomSyntax.two rO body) (v 0) B f).conj
    ((typedAt 2 5 w (SyntaxAtomSyntax.two rM (v 0)) (v 1) B f).conj
      ((typedAt 1 10 w (fun _ => v 1) (v 2) A f).conj
        ((typedAt 2 7 w (SyntaxAtomSyntax.two qO (v 2)) (v 3) A f).conj
          ((typedAt 2 7 w (SyntaxAtomSyntax.two qM (v 3)) (v 4) A f).conj
            (typedAt 1 9 w (fun _ => v 4) D a f)))))

theorem shellData_rename {m l} (w a A B f qM qO rM rO body D : Fin m) (v : Fin 5 → Fin m)
    (ρ : Fin m → Fin l) :
    (shellData w a A B f qM qO rM rO body D v).rename ρ =
      shellData (ρ w) (ρ a) (ρ A) (ρ B) (ρ f) (ρ qM) (ρ qO) (ρ rM) (ρ rO) (ρ body) (ρ D)
        (fun i => ρ (v i)) := by
  simp only [shellData, Formula.rename, typedAt_rename, SyntaxAtomSyntax.two_map]

private def shellBody {m} (w a A B f qM qO rM rO body D : Fin m) : Formula (m+5) :=
  shellData (old 5 w) (old 5 a) (old 5 A) (old 5 B) (old 5 f) (old 5 qM) (old 5 qO)
    (old 5 rM) (old 5 rO) (old 5 body) (old 5 D) (slot 5)

def shell {m} (w a A B f qM qO rM rO body D : Fin m) : Formula m :=
  existsMany 5 (shellBody w a A B f qM qO rM rO body D)

theorem shell_rename {m l} (w a A B f qM qO rM rO body D : Fin m) (ρ : Fin m → Fin l) :
    (shell w a A B f qM qO rM rO body D).rename ρ =
      shell (ρ w) (ρ a) (ρ A) (ρ B) (ρ f) (ρ qM) (ρ qO) (ρ rM) (ρ rO) (ρ body) (ρ D) := by
  simp only [shell, shellBody, existsMany_rename, shellData_rename, lift_old, lift_slot]

private def existsShell {m} (w a A B f qM qO rM rO body : Fin m) : Formula m :=
  .ex (shell w.castSucc a.castSucc A.castSucc B.castSucc f.castSucc qM.castSucc qO.castSucc
    rM.castSucc rO.castSucc body.castSucc (Fin.last m))

private theorem existsShell_rename {m l} (w a A B f qM qO rM rO body : Fin m) (ρ : Fin m → Fin l) :
    (existsShell w a A B f qM qO rM rO body).rename ρ =
      existsShell (ρ w) (ρ a) (ρ A) (ρ B) (ρ f) (ρ qM) (ρ qO) (ρ rM) (ρ rO) (ρ body) := by
  simp only [existsShell, Formula.rename, shell_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem with_constructor {m} {Γ : Context m} {out : Formula m}
    (hZ : ZFContext.Evidence Γ) (arity tag : Nat) (w b f : Fin m) (xs : Fin arity → Fin m)
    (he : Derives Γ (typedFiber arity tag w xs b f))
    (use :
      let T := (Formula.mem (Fin.last m) w.castSucc).conj
        (typedAt arity tag w.castSucc (fun i => (xs i).castSucc) (Fin.last m) b.castSucc f.castSucc)
      let Δ := Context.add T (Context.image Formula.raise Γ)
      ZFContext.Evidence Δ →
      (∀ {p : Formula m}, Derives Γ p → Derives Δ (p.rename Fin.castSucc)) →
      Derives Δ (typedAt arity tag w.castSucc (fun i => (xs i).castSucc) (Fin.last m) b.castSucc f.castSucc) →
      Derives Δ (out.rename Fin.castSucc)) : Derives Γ out := by
  apply with_witness hZ (FormulaCodeConstruct.exists_of_fiber arity tag w xs b f he)
  intro Δ hZ1 lift hT
  exact use hZ1 lift (.conjR hT)

private theorem intro_shell {m} {Γ : Context m} (w a A B f qM qO rM rO body D : Fin m)
    (v : Fin 5 → Fin m) (h : Derives Γ (shellData w a A B f qM qO rM rO body D v)) :
    Derives Γ (shell w a A B f qM qO rM rO body D) := by
  apply HornBinderRules.intro_many 5 (shellBody w a A B f qM qO rM rO body D) v
  exact of_eq (by simp only [shellBody, shellData_rename, assign_old, assign_slot]) h

private theorem shell_total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B f qM qO rM rO body : Fin m) (hw : Derives Γ (omega w))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A))
    (ca : Derives Γ (SyntaxTermSyntax.contexts w a f))
    (cA : Derives Γ (SyntaxTermSyntax.contexts w A f))
    (cB : Derives Γ (SyntaxTermSyntax.contexts w B f))
    (hqM : Derives Γ (formulaCode w qM A f)) (hqO : Derives Γ (formulaCode w qO A f))
    (hrM : Derives Γ (formulaCode w rM B f)) (hrO : Derives Γ (formulaCode w rO B f))
    (hbody : Derives Γ (formulaCode w body B f)) :
    Derives Γ (existsShell w a A B f qM qO rM rO body) := by
  apply with_constructor hZ 2 5 w B f (SyntaxAtomSyntax.two rO body)
    (FormulaCodeConstructors.binary0 hZ w B f rO body
      hw (.conjI cB (.conjI hrO hbody)))
  intro T1 Δ1 hZ1 lift1 h0
  rw [existsShell_rename]
  apply with_constructor hZ1 2 5 w.castSucc B.castSucc f.castSucc (SyntaxAtomSyntax.two rM.castSucc (Fin.last m))
    (FormulaCodeConstructors.binary0 hZ1 w.castSucc B.castSucc f.castSucc rM.castSucc (Fin.last m)
      (by simpa only [omega_rename] using (lift1 hw)) (.conjI (by simpa only [SyntaxTermSyntax.contexts_rename] using (lift1 cB)) (.conjI (by simpa only [formulaCode_rename] using (lift1 hrM)) (.conjR h0))))
  intro T2 Δ2 hZ2 lift2 h1
  rw [existsShell_rename]
  apply with_constructor hZ2 1 10 w.castSucc.castSucc A.castSucc.castSucc f.castSucc.castSucc (fun _ => (Fin.last (m + 1)))
    (FormulaCodeConstructors.existential hZ2 w.castSucc.castSucc A.castSucc.castSucc f.castSucc.castSucc (Fin.last (m + 1))
      (by simpa only [omega_rename] using (lift2 (lift1 hw))) (.conjI (by simpa only [SyntaxTermSyntax.contexts_rename] using (lift2 (lift1 cA)))
      (FormulaCodeRecursiveSyntax.intro_advanced w.castSucc.castSucc (Fin.last (m + 1)) A.castSucc.castSucc f.castSucc.castSucc B.castSucc.castSucc
        (by simpa only [successor_rename] using (lift2 (lift1 hB))) (.conjR h1))))
  intro T3 Δ3 hZ3 lift3 h2
  rw [existsShell_rename]
  apply with_constructor hZ3 2 7 w.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc (SyntaxAtomSyntax.two qO.castSucc.castSucc.castSucc (Fin.last (m + 2)))
    (FormulaCodeConstructors.binary2 hZ3 w.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc qO.castSucc.castSucc.castSucc (Fin.last (m + 2))
      (by simpa only [omega_rename] using (lift3 (lift2 (lift1 hw)))) (.conjI (by simpa only [SyntaxTermSyntax.contexts_rename] using (lift3 (lift2 (lift1 cA)))) (.conjI (by simpa only [formulaCode_rename] using (lift3 (lift2 (lift1 hqO)))) (.conjR h2))))
  intro T4 Δ4 hZ4 lift4 h3
  rw [existsShell_rename]
  apply with_constructor hZ4 2 7 w.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc (SyntaxAtomSyntax.two qM.castSucc.castSucc.castSucc.castSucc (Fin.last (m + 3)))
    (FormulaCodeConstructors.binary2 hZ4 w.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc qM.castSucc.castSucc.castSucc.castSucc (Fin.last (m + 3))
      (by simpa only [omega_rename] using (lift4 (lift3 (lift2 (lift1 hw))))) (.conjI (by simpa only [SyntaxTermSyntax.contexts_rename] using (lift4 (lift3 (lift2 (lift1 cA))))) (.conjI (by simpa only [formulaCode_rename] using (lift4 (lift3 (lift2 (lift1 hqM))))) (.conjR h3))))
  intro T5 Δ5 hZ5 lift5 h4
  rw [existsShell_rename]
  apply with_constructor hZ5 1 9 w.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc.castSucc (fun _ => (Fin.last (m + 4)))
    (FormulaCodeConstructors.universal hZ5 w.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m + 4))
      (by simpa only [omega_rename] using (lift5 (lift4 (lift3 (lift2 (lift1 hw)))))) (.conjI (by simpa only [SyntaxTermSyntax.contexts_rename] using (lift5 (lift4 (lift3 (lift2 (lift1 ca))))))
      (FormulaCodeRecursiveSyntax.intro_advanced w.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m + 4)) a.castSucc.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc.castSucc
        (by simpa only [successor_rename] using (lift5 (lift4 (lift3 (lift2 (lift1 hA)))))) (.conjR h4))))
  intro T6 Δ6 _ lift6 h5
  rw [existsShell_rename]

  apply Derives.exI (Fin.last (m+5))
  simp only [Formula.instantiate, shell_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  let v : Fin 5 → Fin (m+6) :=
    Fin.cases (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc
      (Fin.cases (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc
        (Fin.cases (Fin.last (m+2)).castSucc.castSucc.castSucc
          (Fin.cases (Fin.last (m+3)).castSucc.castSucc (fun _ => (Fin.last (m+4)).castSucc))))
  apply intro_shell _ _ _ _ _ _ _ _ _ _ _ v
  refine .conjI ?_ (.conjI ?_ (.conjI ?_ (.conjI ?_ (.conjI ?_ h5))))
  · have ht := (lift6 (lift5 (lift4 (lift3 (lift2 h0)))))
    simp only [typedAt_rename, SyntaxAtomSyntax.two_map] at ht
    exact ht
  · have ht := (lift6 (lift5 (lift4 (lift3 h1))))
    simp only [typedAt_rename, SyntaxAtomSyntax.two_map] at ht
    exact ht
  · have ht := (lift6 (lift5 (lift4 h2)))
    simp only [typedAt_rename] at ht
    exact ht
  · have ht := (lift6 (lift5 h3))
    simp only [typedAt_rename, SyntaxAtomSyntax.two_map] at ht
    exact ht
  · have ht := (lift6 h4)
    simp only [typedAt_rename, SyntaxAtomSyntax.two_map] at ht
    exact ht


/-- The actual common head, guards, rebound child and constructor trace. -/
def data {n m} (R : Source.Formula (n+2)) (w a A B f j N D : Fin m) (v : Fin 7 → Fin m) : Formula m :=
  (SyntaxMixedImageHead.head w B f (v 0) (v 1)).conj
    ((ForcingGuardCode.compiled false R w A f (v 1) (v 2)).conj
      ((ForcingGuardCode.compiled true R w A f (v 1) (v 3)).conj
        ((ForcingGuardCode.compiled false R w B f (v 1) (v 4)).conj
          ((ForcingExistGuardsCode.compiled R w A B f j (v 5)).conj
            ((rebound w a A B f j N (v 6)).conj
              (shell w a A B f (v 2) (v 3) (v 4) (v 5) (v 6) D))))))

theorem data_rename {n m l} (R : Source.Formula (n+2)) (w a A B f j N D : Fin m) (v : Fin 7 → Fin m)
    (ρ : Fin m → Fin l) :
    (data R w a A B f j N D v).rename ρ =
      data R (ρ w) (ρ a) (ρ A) (ρ B) (ρ f) (ρ j) (ρ N) (ρ D) (fun i => ρ (v i)) := by
  simp only [data, Formula.rename, SyntaxMixedImageHead.head_rename, ForcingGuardCode.compiled_rename,
    ForcingExistGuardsCode.compiled_rename, rebound_rename, shell_rename]

def body {n m} (R : Source.Formula (n+2)) (w a A B f j N D : Fin m) : Formula (m+7) :=
  data R (old 7 w) (old 7 a) (old 7 A) (old 7 B) (old 7 f) (old 7 j) (old 7 N) (old 7 D) (slot 7)

def compiled {n m} (R : Source.Formula (n+2)) (w a A B f j N D : Fin m) : Formula m :=
  existsMany 7 (body R w a A B f j N D)

theorem compiled_rename {n m l} (R : Source.Formula (n+2)) (w a A B f j N D : Fin m) (ρ : Fin m → Fin l) :
    (compiled R w a A B f j N D).rename ρ =
      compiled R (ρ w) (ρ a) (ρ A) (ρ B) (ρ f) (ρ j) (ρ N) (ρ D) := by
  simp only [compiled, body, existsMany_rename, data_rename, lift_old, lift_slot]

def existsCompiled {n m} (R : Source.Formula (n+2)) (w a A B f j N : Fin m) : Formula m :=
  .ex (compiled R w.castSucc a.castSucc A.castSucc B.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m))

theorem existsCompiled_rename {n m l} (R : Source.Formula (n+2)) (w a A B f j N : Fin m) (ρ : Fin m → Fin l) :
    (existsCompiled R w a A B f j N).rename ρ =
      existsCompiled R (ρ w) (ρ a) (ρ A) (ρ B) (ρ f) (ρ j) (ρ N) := by
  simp only [existsCompiled, Formula.rename, compiled_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem with_guards {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (w a A B f j N z t qM qO rM rO C : Fin m)
    (hw : Derives Γ (omega w)) (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A))
    (hN : Derives Γ (formulaCode w N a f))
    (hh : Derives Γ (SyntaxMixedImageHead.head w B f z t))
    (hqM : Derives Γ (ForcingGuardCode.compiled false R w A f t qM))
    (hqO : Derives Γ (ForcingGuardCode.compiled true R w A f t qO))
    (hrM : Derives Γ (ForcingGuardCode.compiled false R w B f t rM))
    (hrO : Derives Γ (ForcingExistGuardsCode.compiled R w A B f j rO))
    (hC : Derives Γ (rebound w a A B f j N C)) :
    Derives Γ (existsCompiled R w a A B f j N) := by
  have ca := Derives.conjR (FormulaCodeProperties.guards w N a f hN)
  have hAr := OmegaStructureAlgebra.successor_member w A a (ZFContext.arithmetic hZ).base.extensionality
    hw (.conjL ca) hA
  have hBr := OmegaStructureAlgebra.successor_member w B A (ZFContext.arithmetic hZ).base.extensionality hw hAr hB
  let P := shell w.castSucc a.castSucc A.castSucc B.castSucc f.castSucc qM.castSucc qO.castSucc
    rM.castSucc rO.castSucc C.castSucc (Fin.last m)
  apply with_witness (P := P) hZ
    (shell_total hZ w a A B f qM qO rM rO C hw hA hB ca (.conjI hAr (.conjR ca)) (.conjI hBr (.conjR ca))
      (ForcingGuardCode.compiled_type false R w A f t qM hqM)
      (ForcingGuardCode.compiled_type true R w A f t qO hqO)
      (ForcingGuardCode.compiled_type false R w B f t rM hrM)
      (ForcingExistGuardsCode.compiled_type R w A B f j rO hrO) (rebound_type hZ w a A B f j N C hC))
  intro Δ _ lift hP
  rw [existsCompiled_rename]
  apply Derives.exI (Fin.last m)
  simp only [Formula.instantiate, compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  let v : Fin 7 → Fin (m+1) := Fin.cases z.castSucc (Fin.cases t.castSucc
    (Fin.cases qM.castSucc (Fin.cases qO.castSucc (Fin.cases rM.castSucc
      (SetLanguage.args2 rO.castSucc C.castSucc)))))
  apply HornBinderRules.intro_many 7 (body R _ _ _ _ _ _ _ _) v
  have hd : Derives Δ (data R w.castSucc a.castSucc A.castSucc B.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m) v) := by
    exact .conjI (of_eq (SyntaxMixedImageHead.head_rename _ _ _ _ _ _) (lift hh))
      (.conjI (of_eq (ForcingGuardCode.compiled_rename false R _ _ _ _ _ _) (lift hqM))
        (.conjI (of_eq (ForcingGuardCode.compiled_rename true R _ _ _ _ _ _) (lift hqO))
          (.conjI (of_eq (ForcingGuardCode.compiled_rename false R _ _ _ _ _ _) (lift hrM))
            (.conjI (of_eq (ForcingExistGuardsCode.compiled_rename R _ _ _ _ _ _ _) (lift hrO))
              (.conjI (of_eq (rebound_rename _ _ _ _ _ _ _ _ _) (lift hC)) hP)))))

  exact of_eq (by simp only [body, data_rename, assign_old, assign_slot]) hd

private theorem from_head {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (w a A B f j N z t : Fin m)
    (hw : Derives Γ (omega w)) (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (n+1) j))
    (hN : Derives Γ (formulaCode w N a f))
    (hh : Derives Γ (SyntaxMixedImageHead.head w B f z t)) : Derives Γ (existsCompiled R w a A B f j N) := by
  have ha := Derives.conjL (Derives.conjR (FormulaCodeProperties.guards w N a f hN))
  have hnatF := SyntaxNumerals.range hZ (n+2) w f hw hf
  have hnatA := OmegaStructureAlgebra.successor_member w A a (ZFContext.arithmetic hZ).base.extensionality hw ha hA
  have hzero := Derives.conjL (Derives.conjR hh)
  have htA := SyntaxMixedImageHead.term_at_zero hZ w a A f z t hw ha hnatF hA (.conjL hh) hzero
  have htB := SyntaxMixedImageHead.term_at_zero hZ w A B f z t hw hnatA hnatF hB (.conjL hh) hzero
  let Mq := ForcingGuardCode.compiled false R w.castSucc A.castSucc f.castSucc t.castSucc (Fin.last m)
  apply with_witness (P := Mq) hZ (ForcingGuardCode.total hZ false R w A f t hw hf htA)
  intro Δ1 hZ1 lift1 hMq
  rw [existsCompiled_rename]
  let Oq := ForcingGuardCode.compiled true R w.castSucc.castSucc A.castSucc.castSucc f.castSucc.castSucc
    t.castSucc.castSucc (Fin.last (m+1))
  apply with_witness (P := Oq) hZ1
    (ForcingGuardCode.total hZ1 true R w.castSucc A.castSucc f.castSucc t.castSucc
      (of_eq (omega_rename _ _) (lift1 hw))
      (of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) _ _) (lift1 hf))
      (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ _) (lift1 htA)))
  intro Δ2 hZ2 lift2 hOq
  rw [existsCompiled_rename]
  let Mr := ForcingGuardCode.compiled false R w.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc
    f.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc (Fin.last (m+2))
  apply with_witness (P := Mr) hZ2
    (ForcingGuardCode.total hZ2 false R w.castSucc.castSucc B.castSucc.castSucc f.castSucc.castSucc
      t.castSucc.castSucc
      (by simpa only [omega_rename] using lift2 (lift1 hw))
      (by simpa only [SyntaxNumeralSyntax.numeral_rename] using lift2 (lift1 hf))
      (by simpa only [SyntaxTermSyntax.term_rename] using lift2 (lift1 htB)))
  intro Δ3 hZ3 lift3 hMr
  rw [existsCompiled_rename]
  let Or := ForcingExistGuardsCode.compiled R w.castSucc.castSucc.castSucc.castSucc
    A.castSucc.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc.castSucc
    f.castSucc.castSucc.castSucc.castSucc j.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3))
  apply with_witness (P := Or) hZ3
    (ForcingExistGuardsCode.total hZ3 R w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc
      A.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc j.castSucc.castSucc.castSucc
      (by simpa only [omega_rename] using lift3 (lift2 (lift1 hw))) (lift3 (lift2 (lift1 ha)))
      (by simpa only [successor_rename] using lift3 (lift2 (lift1 hA)))
      (by simpa only [successor_rename] using lift3 (lift2 (lift1 hB)))
      (by simpa only [SyntaxNumeralSyntax.numeral_rename] using lift3 (lift2 (lift1 hf)))
      (by simpa only [SyntaxNumeralSyntax.numeral_rename] using lift3 (lift2 (lift1 hj))))
  intro Δ4 hZ4 lift4 hOr
  rw [existsCompiled_rename]
  let C := rebound w.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc
    A.castSucc.castSucc.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc.castSucc.castSucc
    f.castSucc.castSucc.castSucc.castSucc.castSucc j.castSucc.castSucc.castSucc.castSucc.castSucc
    N.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4))
  apply with_witness (P := C) hZ4
    (rebound_total hZ4 w.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc
      A.castSucc.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc
      j.castSucc.castSucc.castSucc.castSucc N.castSucc.castSucc.castSucc.castSucc
      (by simpa only [omega_rename] using lift4 (lift3 (lift2 (lift1 hw))))
      (by simpa only [successor_rename] using lift4 (lift3 (lift2 (lift1 hA))))
      (by simpa only [successor_rename] using lift4 (lift3 (lift2 (lift1 hB))))
      (by simpa only [formulaCode_rename] using lift4 (lift3 (lift2 (lift1 hN)))))
  intro Δ5 hZ5 lift5 hC
  rw [existsCompiled_rename]
  exact with_guards hZ5 R _ _ _ _ _ _ _ z.castSucc.castSucc.castSucc.castSucc.castSucc
    t.castSucc.castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc
    (Fin.last (m+2)).castSucc.castSucc (Fin.last (m+3)).castSucc (Fin.last (m+4))
    (by simpa only [omega_rename] using lift5 (lift4 (lift3 (lift2 (lift1 hw)))))
    (by simpa only [successor_rename] using lift5 (lift4 (lift3 (lift2 (lift1 hA)))))
    (by simpa only [successor_rename] using lift5 (lift4 (lift3 (lift2 (lift1 hB)))))
    (by simpa only [formulaCode_rename] using lift5 (lift4 (lift3 (lift2 (lift1 hN)))))
    (by simpa only [SyntaxMixedImageHead.head_rename] using lift5 (lift4 (lift3 (lift2 (lift1 hh)))))
    (by simpa only [Mq, ForcingGuardCode.compiled_rename] using lift5 (lift4 (lift3 (lift2 hMq))))
    (by simpa only [Oq, ForcingGuardCode.compiled_rename] using lift5 (lift4 (lift3 hOq)))
    (by simpa only [Mr, ForcingGuardCode.compiled_rename] using lift5 (lift4 hMr))
    (by simpa only [Or, ForcingExistGuardsCode.compiled_rename] using lift5 hOr) hC

/-- Build the original density hypothesis for every valid internal forcing
output code. No standard-code or supplied witness-output condition. -/
theorem total {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (w a A B f j N : Fin m)
    (hw : Derives Γ (omega w)) (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (n+1) j))
    (hN : Derives Γ (formulaCode w N a f)) : Derives Γ (existsCompiled R w a A B f j N) := by
  have ha := Derives.conjL (Derives.conjR (FormulaCodeProperties.guards w N a f hN))
  have hnatA := OmegaStructureAlgebra.successor_member w A a (ZFContext.arithmetic hZ).base.extensionality hw ha hA
  let P := SyntaxMixedImageHead.head (old 2 w) (old 2 B) (old 2 f) (slot 2 0) (slot 2 1)
  apply HornBinderRules.eliminate_many 2 P _
    (SyntaxMixedImageHead.exists_head hZ w A B f hw hnatA (SyntaxNumerals.range hZ (n+2) w f hw hf) hB)
  have hP : Derives (Context.add P (raisedContext 2 Γ)) P := .hyp (Or.inl rfl)
  let ρ := old (m := m) 2
  exact of_eq (existsCompiled_rename R w a A B f j N ρ).symm
    (from_head (HornBinderRules.zf_body 2 hZ P) R (ρ w) (ρ a) (ρ A) (ρ B) (ρ f) (ρ j) (ρ N) (slot 2 0) (slot 2 1)
      (of_eq (omega_rename _ _) (HornBinderRules.under_body 2 hw P))
      (of_eq (successor_rename _ _ _) (HornBinderRules.under_body 2 hA P))
      (of_eq (successor_rename _ _ _) (HornBinderRules.under_body 2 hB P))
      (of_eq (SyntaxNumeralSyntax.numeral_rename (n+2) _ _) (HornBinderRules.under_body 2 hf P))
      (of_eq (SyntaxNumeralSyntax.numeral_rename (n+1) _ _) (HornBinderRules.under_body 2 hj P))
      (of_eq (formulaCode_rename _ _ _ _ _) (HornBinderRules.under_body 2 hN P)) hP)

def sentence {n m} (R : Source.Formula (n+2)) (w a A B f j N : Fin m) : Source.Sentence :=
  ((omega w).imp ((successor A a).imp ((successor B A).imp
    ((SyntaxNumeralSyntax.numeral (n+2) f).imp ((SyntaxNumeralSyntax.numeral (n+1) j).imp
      ((formulaCode w N a f).imp (existsCompiled R w a A B f j N))))))).close

theorem kernel_certificate {n m} (R : Source.Formula (n+2)) (w a A B f j N : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence R w a A B f j N)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  repeat apply Derives.impI
  exact total (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add
    (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _) _) _) R w a A B f j N
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))


private theorem shell_type {m} {Γ : Context m} (w a A B f qM qO rM rO C D : Fin m)
    (h : Derives Γ (shell w a A B f qM qO rM rO C D)) :
    Derives Γ (formulaCode w D a f) := by
  let P := shellBody w a A B f qM qO rM rO C D
  apply HornBinderRules.eliminate_many 5 P _ h
  have hP : Derives (Context.add P (raisedContext 5 Γ)) P := .hyp (Or.inl rfl)
  have ht : Derives (Context.add P (raisedContext 5 Γ)) (formulaCode (old 5 w) (old 5 D) (old 5 a) (old 5 f)) :=
    .conjR (.conjR (.conjR (.conjR (.conjR (.conjR hP)))))
  exact of_eq (formulaCode_rename w D a f (old 5)).symm ht

theorem compiled_type {n m} {Γ : Context m} (R : Source.Formula (n+2)) (w a A B f j N D : Fin m)
    (h : Derives Γ (compiled R w a A B f j N D)) : Derives Γ (formulaCode w D a f) := by
  let P := body R w a A B f j N D
  apply HornBinderRules.eliminate_many 7 P _ h
  have hP : Derives (Context.add P (raisedContext 7 Γ)) P := .hyp (Or.inl rfl)
  exact of_eq (formulaCode_rename w D a f (old 7)).symm
    (shell_type (old 7 w) (old 7 a) (old 7 A) (old 7 B) (old 7 f)
      (slot 7 2) (slot 7 3) (slot 7 4) (slot 7 5) (slot 7 6) (old 7 D)
      (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hP)))))))

def queryData {n m} (R : Source.Formula (n+2)) (w a A B f j N b d L S D Q : Fin m) : Formula m :=
  (compiled R w a A B f j N D).conj (substituted w L S a f b d D Q)

theorem queryData_rename {n m l} (R : Source.Formula (n+2)) (w a A B f j N b d L S D Q : Fin m)
    (ρ : Fin m → Fin l) :
    (queryData R w a A B f j N b d L S D Q).rename ρ =
      queryData R (ρ w) (ρ a) (ρ A) (ρ B) (ρ f) (ρ j) (ρ N) (ρ b) (ρ d) (ρ L) (ρ S) (ρ D) (ρ Q) := by
  simp only [queryData, Formula.rename, compiled_rename, substituted_rename]

def queried {n m} (R : Source.Formula (n+2)) (w a A B f j N b d L S : Fin m) : Formula m :=
  existsMany 2 (queryData R (old 2 w) (old 2 a) (old 2 A) (old 2 B) (old 2 f) (old 2 j)
    (old 2 N) (old 2 b) (old 2 d) (old 2 L) (old 2 S) (slot 2 0) (slot 2 1))

theorem queried_rename {n m l} (R : Source.Formula (n+2)) (w a A B f j N b d L S : Fin m) (ρ : Fin m → Fin l) :
    (queried R w a A B f j N b d L S).rename ρ =
      queried R (ρ w) (ρ a) (ρ A) (ρ B) (ρ f) (ρ j) (ρ N) (ρ b) (ρ d) (ρ L) (ρ S) := by
  simp only [queried, existsMany_rename, queryData_rename, lift_old, lift_slot]

/-- Read the density hypothesis under the same actual substitution lists as
the selected condition's forcing output. Both codes stay available. -/
theorem from_tables {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (n+2)) (w a A B f j N b d L S : Fin m)
    (hw : Derives Γ (omega w)) (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (n+1) j))
    (hN : Derives Γ (formulaCode w N a f))
    (hTables : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a f b d L S)) :
    Derives Γ (queried R w a A B f j N b d L S) := by
  let P := compiled R w.castSucc a.castSucc A.castSucc B.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m)
  apply with_witness (P := P) hZ (total hZ R w a A B f j N hw hA hB hf hj hN)
  intro Δ1 hZ1 lift1 hP
  rw [queried_rename]
  have ht := compiled_type R w.castSucc a.castSucc A.castSucc B.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m) hP
  have hi : Derives Δ1 (SyntaxMixedFormulaOutputSyntax.input w.castSucc L.castSucc S.castSucc
      a.castSucc f.castSucc b.castSucc d.castSucc (Fin.last m)) :=
    .conjI ht (of_eq (SyntaxMixedImageCodeSyntax.termLists_rename _ _ _ _ _ _ _ _) (lift1 hTables))
  let Q := substituted w.castSucc.castSucc L.castSucc.castSucc S.castSucc.castSucc
    a.castSucc.castSucc f.castSucc.castSucc b.castSucc.castSucc d.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1))
  apply with_witness (P := Q) hZ1
    (SyntaxMixedFormulaOutputInduction.actual_exists hZ1 w.castSucc L.castSucc S.castSucc
      a.castSucc f.castSucc b.castSucc d.castSucc (Fin.last m) (of_eq (omega_rename _ _) (lift1 hw)) hi)
  intro Δ2 _ lift2 hQ
  rw [queried_rename]
  apply HornBinderRules.intro_many 2 _ (SetLanguage.args2 (Fin.last m).castSucc (Fin.last (m+1)))
  have hd : Derives Δ2 (queryData R w.castSucc.castSucc a.castSucc.castSucc A.castSucc.castSucc
      B.castSucc.castSucc f.castSucc.castSucc j.castSucc.castSucc N.castSucc.castSucc b.castSucc.castSucc
      d.castSucc.castSucc L.castSucc.castSucc S.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))) :=
    .conjI (of_eq (compiled_rename R _ _ _ _ _ _ _ _ _) (lift2 hP)) hQ
  exact of_eq (by simp only [queryData_rename, assign_old, assign_slot]; rfl) hd


private theorem weakened_nullary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool)
    (w a A f N W : Fin m) (hw : Derives Γ (omega w))
    (hN : Derives Γ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 N))
    (hW : Derives Γ (weakened w a A f N W)) : Derives Γ (.equal W N) := by
  let P := weakenBody w a A f N W
  apply HornBinderRules.eliminate_many 3 P _ hW
  have hP : Derives (Context.add P (raisedContext 3 Γ)) P := .hyp (Or.inl rfl)
  have hN3 := of_eq (by simp only [SyntaxNodeSyntax.constructor_rename]; rfl)
    (HornBinderRules.under_body 3 hN P)
  exact SyntaxMixedFormulaNullary.unique (HornBinderRules.zf_body 3 hZ P) truth (old 3 w)
    (slot 3 1) (slot 3 2) (old 3 a) (old 3 f) (old 3 A) (old 3 f) (old 3 N) (old 3 W)
    (of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw P)) hN3
    (.conjR (.conjR (.conjR hP)))

private theorem rebound_nullary_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool)
    (w A B f j N W Q : Fin m) (hw : Derives Γ (omega w))
    (hN : Derives Γ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 N))
    (he : Derives Γ (.equal W N))
    (hQ : Derives Γ (ForcingConditionRebind.compiled w A f B j W Q)) : Derives Γ (.equal Q N) := by
  let P : Formula (m+6) := ForcingConditionRebind.data (old 6 w) (old 6 A) (old 6 f) (old 6 B)
    (old 6 j) (old 6 W) (old 6 Q) (slot 6)
  change Derives Γ (existsMany 6 P) at hQ
  apply HornBinderRules.eliminate_many 6 P _ hQ
  have hP : Derives (Context.add P (raisedContext 6 Γ)) P := .hyp (Or.inl rfl)
  have hN6 := of_eq (by simp only [SyntaxNodeSyntax.constructor_rename]; rfl)
    (HornBinderRules.under_body 6 hN P)
  have hs := SyntaxMixedFormulaJudgmentSubst.subst_n (old 6 w) (slot 6 3) (slot 6 5)
    (old 6 A) (old 6 f) (old 6 B) (old 6 f) (old 6 W) (old 6 Q) (old 6 N)
    (HornBinderRules.under_body 6 he P) (.conjR (.conjR (.conjR hP)))
  exact SyntaxMixedFormulaNullary.unique (HornBinderRules.zf_body 6 hZ P) truth (old 6 w)
    (slot 6 3) (slot 6 5) (old 6 A) (old 6 f) (old 6 B) (old 6 f) (old 6 N) (old 6 Q)
    (of_eq (omega_rename w (old 6)) (HornBinderRules.under_body 6 hw P)) hN6 hs

/-- A constant keeps its exact code across both actual density substitutions. -/
theorem rebound_nullary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool)
    (w a A B f j N Q : Fin m) (hw : Derives Γ (omega w))
    (hN : Derives Γ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 N))
    (hQ : Derives Γ (rebound w a A B f j N Q)) : Derives Γ (.equal Q N) := by
  unfold rebound at hQ
  apply with_witness hZ hQ
  intro Δ hZ1 lift hP
  have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
  have hN1 := of_eq (by simp only [SyntaxNodeSyntax.constructor_rename]; rfl) (lift hN)
  have he := weakened_nullary hZ1 truth w.castSucc a.castSucc A.castSucc f.castSucc N.castSucc
    (Fin.last m) hw1 hN1 (.conjL hP)
  exact rebound_nullary_at hZ1 truth w.castSucc A.castSucc B.castSucc f.castSucc j.castSucc N.castSucc
    (Fin.last m) Q.castSucc hw1 hN1 he (.conjR hP)

/-- The actual density record, with its exact constant witness-body code. -/
def nullaryTrace {n m} (R : Source.Formula (n+2)) (w a A B f j N D : Fin m) : Formula m :=
  existsMany 7 ((body R w a A B f j N D).conj (.equal (slot 7 6) (old 7 N)))

theorem nullaryTrace_rename {n m l} (R : Source.Formula (n+2)) (w a A B f j N D : Fin m)
    (ρ : Fin m → Fin l) :
    (nullaryTrace R w a A B f j N D).rename ρ =
      nullaryTrace R (ρ w) (ρ a) (ρ A) (ρ B) (ρ f) (ρ j) (ρ N) (ρ D) := by
  simp only [nullaryTrace, existsMany_rename, Formula.rename, body, data_rename, lift_old, lift_slot]

/-- Consume the same compiler execution; its witness body is the input constant. -/
theorem nullary_trace {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool)
    (R : Source.Formula (n+2)) (w a A B f j N D : Fin m) (hw : Derives Γ (omega w))
    (hN : Derives Γ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 N))
    (hD : Derives Γ (compiled R w a A B f j N D)) : Derives Γ (nullaryTrace R w a A B f j N D) := by
  let P := body R w a A B f j N D
  let Δ := Context.add P (raisedContext 7 Γ)
  apply HornBinderRules.eliminate_many 7 P _ hD
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hw7 := of_eq (omega_rename w (old 7)) (HornBinderRules.under_body 7 hw P)
  have hN7 := of_eq (by simp only [SyntaxNodeSyntax.constructor_rename]; rfl)
    (HornBinderRules.under_body 7 hN P)
  have hc := rebound_nullary (HornBinderRules.zf_body 7 hZ P) truth (old 7 w) (old 7 a) (old 7 A)
    (old 7 B) (old 7 f) (old 7 j) (old 7 N) (slot 7 6) hw7 hN7
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hP))))))
  apply of_eq (nullaryTrace_rename R w a A B f j N D (old 7)).symm
  apply HornBinderRules.intro_many 7 _ (slot 7)
  exact of_eq (by simp only [P, body, Formula.rename, data_rename, assign_old, assign_slot])
    (.conjI hP hc : Derives Δ (P.conj (.equal (slot 7 6) (old 7 N))))

end PPAC.Migration.ForcingDensityCode
