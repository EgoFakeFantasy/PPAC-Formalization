import PPAC.Migration.OriginalAxiomCodeTest
import PPAC.Migration.Internal.PureQuotationTypedFormulas

/-! Correctness against ORIGINAL Project/native quotation. External syntax
indexes a proof scheme; each conclusion is an actual object derivation and
quantifies arbitrary internal candidate codes. This is not a uniform internal
truth predicate or the completed internal Proof/Con theorem. -/
namespace PPAC.Migration.ProjectCompilerQuotation
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree leaf)
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
attribute [local irreducible] NaturalRecursionSyntax.matrix
attribute [local implicit_reducible] YesMetaZFC.SetTheory.signature

/-- Finite syntax fields are produced by the EXISTING tree-quotation theorem.
The external block length never indexes an internal parameter count. -/
private def quotes {m} : (k : Nat) → (Fin k → Tree) → Fin m → (Fin k → Fin m) → Source.Formula m
  | 0, _, w, _ => .equal w w
  | k+1, ts, w, env => (quotes k (fun i => ts i.castSucc) w (fun i => env i.castSucc)).conj
      (OriginalTreeQuotationSyntax.tree (ts (Fin.last k)) w (env (Fin.last k)))

private theorem quotes_rename {m l} (k : Nat) (ts : Fin k → Tree) (w : Fin m) (env : Fin k → Fin m) (r : Fin m → Fin l) :
    (quotes k ts w env).rename r = quotes k ts (r w) (fun i => r (env i)) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [quotes, Formula.rename, ih, OriginalTreeQuotationSyntax.tree_rename]

private theorem quotes_at {m} {Γ : Context m} (k : Nat) (ts : Fin k → Tree) (w : Fin m) (env : Fin k → Fin m) (i : Fin k)
    (h : Derives Γ (quotes k ts w env)) : Derives Γ (OriginalTreeQuotationSyntax.tree (ts i) w (env i)) := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact .conjR h
    · exact ih (fun a => ts a.castSucc) (fun a => env a.castSucc) j (.conjL h)

private def quoteBody {m} (k : Nat) (ts : Fin k → Tree) (w : Fin m) : Source.Formula (m+k) :=
  quotes k ts (old k w) (slot k)

private theorem quoteBlock_rename {m l} (k : Nat) (ts : Fin k → Tree) (w : Fin m) (r : Fin m → Fin l) :
    (existsMany k (quoteBody k ts w)).rename r = existsMany k (quoteBody k ts (r w)) := by
  simp only [existsMany_rename,quoteBody,quotes_rename,lift_old,lift_slot]

private theorem quote_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (ts : Fin k → Tree) (w : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ (existsMany k (quoteBody k ts w)) := by
  induction k generalizing m with
  | zero => exact .eqRefl w
  | succ k ih =>
    let ts0 : Fin k → Tree := fun i => ts i.castSucc
    let B := quoteBody k ts0 w
    let Δ := Context.add B (raisedContext k Γ)
    apply HornBinderRules.eliminate_many k B _ (ih hZ ts0 w hw)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hZk := HornBinderRules.zf_body k hZ B
    have hwk := of_eq (omega_rename w (old k)) (HornBinderRules.under_body k hw B)
    let C := (Source.Formula.mem (Fin.last (m+k)) (old k w).castSucc).conj
      (OriginalTreeQuotationSyntax.tree (ts (Fin.last k)) (old k w).castSucc (Fin.last (m+k)))
    let Ξ := Context.add C (Context.image Formula.raise Δ)
    apply Derives.exE (p := C) (OriginalTreeQuotationExistence.tree_exists hZk (ts (Fin.last k)) (old k w) hwk)
    have hC : Derives Ξ C := .hyp (Or.inl rfl)
    let env : Fin (k+1) → Fin (m+k+1) := Fin.lastCases (Fin.last (m+k)) (fun i => (slot k i).castSucc)
    have hhead := of_eq (quotes_rename k ts0 (old k w) (slot k) Fin.castSucc) (under hB C)
    have hqs : Derives Ξ (quotes (k+1) ts (old k w).castSucc env) :=
      of_eq (by simp only [quotes,env,ts0,Fin.lastCases_castSucc,Fin.lastCases_last]) (.conjI hhead (.conjR hC))
    have ho : Derives Ξ (existsMany (k+1) (quoteBody (k+1) ts (old k w).castSucc)) := by
      apply HornBinderRules.intro_many (k+1) _ env
      exact of_eq (by simp only [quoteBody, quotes_rename, assign_old, assign_slot]) hqs
    have he : ((existsMany (k+1) (quoteBody (k+1) ts w)).rename (old k)).raise =
        existsMany (k+1) (quoteBody (k+1) ts (old k w).castSucc) := by
      rw [quoteBlock_rename,Formula.raise,quoteBlock_rename]
    exact of_eq he.symm ho

private structure Frame {m} (Γ : Context m) (depth : Nat) (w b z n q : Fin m) (source target : Tree) : Prop where
  zf : ZFContext.Evidence Γ
  omega : Derives Γ (OmegaSyntax.omega w)
  scope : Derives Γ (SyntaxNumeralSyntax.numeral depth b)
  zero : Derives Γ (empty z)
  input : Derives Γ (OriginalTreeQuotationSyntax.tree source w n)
  output : Derives Γ (OriginalTreeQuotationSyntax.tree target w q)

private theorem Frame.under {m} {Γ : Context m} {d : Nat} {w b z n q : Fin m} {s t : Tree}
    (h : Frame Γ d w b z n q s t) (P : Source.Formula (m+1)) :
    Frame (Context.add P (Context.image Formula.raise Γ)) d w.castSucc b.castSucc z.castSucc n.castSucc q.castSucc s t where
  zf := ZFContext.under h.zf P
  omega := of_eq (omega_rename w Fin.castSucc) (SourceLogic.under h.omega P)
  scope := of_eq (SyntaxNumeralSyntax.numeral_rename d b Fin.castSucc) (SourceLogic.under h.scope P)
  zero := of_eq (empty_rename z Fin.castSucc) (SourceLogic.under h.zero P)
  input := of_eq (OriginalTreeQuotationSyntax.tree_rename s w n Fin.castSucc) (SourceLogic.under h.input P)
  output := of_eq (OriginalTreeQuotationSyntax.tree_rename t w q Fin.castSucc) (SourceLogic.under h.output P)

private theorem Frame.body {m} {Γ : Context m} {d : Nat} {w b z n q : Fin m} {s t : Tree}
    (h : Frame Γ d w b z n q s t) (k : Nat) (P : Source.Formula (m+k)) :
    Frame (Context.add P (raisedContext k Γ)) d (old k w) (old k b) (old k z) (old k n) (old k q) s t where
  zf := HornBinderRules.zf_body k h.zf P
  omega := of_eq (omega_rename w (old k)) (HornBinderRules.under_body k h.omega P)
  scope := of_eq (SyntaxNumeralSyntax.numeral_rename d b (old k)) (HornBinderRules.under_body k h.scope P)
  zero := of_eq (empty_rename z (old k)) (HornBinderRules.under_body k h.zero P)
  input := of_eq (OriginalTreeQuotationSyntax.tree_rename s w n (old k)) (HornBinderRules.under_body k h.input P)
  output := of_eq (OriginalTreeQuotationSyntax.tree_rename t w q (old k)) (HornBinderRules.under_body k h.output P)

private def Correct (depth : Nat) (source target : Tree) : Prop :=
  ∀ {m} {Γ : Context m} (w b z n q : Fin m), Frame Γ depth w b z n q source target →
    Derives Γ (ProjectCompilerCodeSyntax.compiled w n b q)

private theorem constant_correct (depth : Nat) (truth : Bool) :
    Correct depth (leaf (SyntaxAtomSyntax.nullaryTag truth)) (leaf (SyntaxAtomSyntax.nullaryTag truth)) := by
  intro m Γ w b z n q h
  have hn := OriginalQuotationNodeFields.tree_to_constructor h.zf _ [] w n Fin.elim0 h.omega (.eqRefl w) h.input
  have he := OriginalTreeQuotationUnique.tree_unique h.zf _ w n q h.omega h.input h.output
  have hc := ProjectCompilerBase.constant_compiled h.zf truth w n b h.omega (SyntaxNumerals.range h.zf depth w b h.omega h.scope) hn
  let P := ProjectCompilerCodeSyntax.compiled w.castSucc n.castSucc b.castSucc (Fin.last m)
  exact of_eq (by simp only [P, Formula.instantiate, ProjectCompilerCodeSyntax.compiled_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (Derives.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, ProjectCompilerCodeSyntax.compiled_rename,
        Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc))

private theorem single_at {m} {Γ : Context m} (depth tag : Nat) (advance : Bool)
    (hs : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (s t : Tree) (ih : Correct (if advance then depth+1 else depth) s t)
    (w b B z n q x y : Fin m) (h : Frame Γ depth w b z n q (.node tag [s]) (.node tag [t]))
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral (if advance then depth+1 else depth) B))
    (hstep : advance = true → Derives Γ (successor B b))
    (hx : Derives Γ (OriginalTreeQuotationSyntax.tree s w x)) (hy : Derives Γ (OriginalTreeQuotationSyntax.tree t w y)) :
    Derives Γ (ProjectCompilerCodeSyntax.compiled w n b q) := by
  have hn := OriginalQuotationNodeFields.tree_to_constructor h.zf tag [s] w n (fun _ => x) h.omega (.conjI hx (.eqRefl w)) h.input
  have hq := OriginalQuotationNodeFields.tree_to_constructor h.zf tag [t] w q (fun _ => y) h.omega (.conjI hy (.eqRefl w)) h.output
  have hc := ih w B z x y ⟨h.zf,h.omega,hB,h.zero,hx,hy⟩
  have hm := SyntaxConstructors.child_member h.zf 1 tag w (fun _ => x) n 0 h.omega hn
  have hquery : Derives Γ (ProjectCompilerCaseSyntax.queried ProjectCompilerRecursiveSyntax.codeMatrix
      (ProjectCompilerRecursiveSyntax.parameters w) n x B y) :=
    .conjI hm (of_eq (ProjectCompilerRecursiveSyntax.codeMatrix_at _ x B y).symm hc)
  have hcheck : Derives Γ (ProjectCompilerCaseSyntax.check advance ProjectCompilerRecursiveSyntax.codeMatrix
      (ProjectCompilerRecursiveSyntax.parameters w) n x b y) := by
    cases advance
    · change Derives Γ (ProjectCompilerCaseSyntax.queried ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) n x b y)
      have hsame := SyntaxNumerals.unique h.zf depth B b hB h.scope
      let P := ProjectCompilerCaseSyntax.queried ProjectCompilerRecursiveSyntax.codeMatrix
        (ProjectCompilerRecursiveSyntax.parameters w.castSucc) n.castSucc x.castSucc (Fin.last m) y.castSucc
      exact of_eq (by simp only [P, Formula.instantiate, ProjectCompilerCaseSyntax.queried_rename, ProjectCompilerRecursiveSyntax.parameters_map,
        Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
          (Derives.eqSubst P hsame (of_eq (by simp only [P, Formula.instantiate, ProjectCompilerCaseSyntax.queried_rename,
            ProjectCompilerRecursiveSyntax.parameters_map, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hquery))
    · apply Derives.exI B
      exact of_eq (by simp only [Formula.instantiate, Formula.rename, successor_rename, ProjectCompilerCaseSyntax.queried_rename,
        ProjectCompilerRecursiveSyntax.parameters_map, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (hstep rfl) hquery)
  have hcase := ProjectCompilerCaseIntro.single_case tag advance ProjectCompilerRecursiveSyntax.codeMatrix
    (ProjectCompilerRecursiveSyntax.parameters w) w b n q x y (.conjI hn (.conjI hcheck hq))
  exact ProjectCompilerCompleteIntro.of_cases h.zf w n b q z h.omega
    (OriginalTreeQuotationProperties.tree_range h.zf _ w n h.omega h.input)
    (SyntaxNumerals.range h.zf depth w b h.omega h.scope)
    (OriginalTreeQuotationProperties.tree_range h.zf _ w q h.omega h.output) h.zero
      (ProjectCompilerCompleteConstructors.single_cases tag advance hs w b z n q hcase)

private theorem single_scoped {m} {Γ : Context m} (depth tag : Nat) (advance : Bool)
    (hs : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (s t : Tree) (ih : Correct (if advance then depth+1 else depth) s t)
    (w b B z n q : Fin m) (h : Frame Γ depth w b z n q (.node tag [s]) (.node tag [t]))
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral (if advance then depth+1 else depth) B))
    (hstep : advance = true → Derives Γ (successor B b)) :
    Derives Γ (ProjectCompilerCodeSyntax.compiled w n b q) := by
  let ts : Fin 2 → Tree := Fin.cases s (fun _ => t)
  let K := quoteBody 2 ts w
  let Δ := Context.add K (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 K _ (quote_exists h.zf 2 ts w h.omega)
  have hK : Derives Δ K := .hyp (Or.inl rfl)
  have hh := h.body 2 K
  have hB2 := of_eq (SyntaxNumeralSyntax.numeral_rename _ B (old 2)) (HornBinderRules.under_body 2 hB K)
  have hstep2 : advance = true → Derives Δ (successor (old 2 B) (old 2 b)) := fun he =>
    of_eq (successor_rename B b (old 2)) (HornBinderRules.under_body 2 (hstep he) K)
  exact of_eq (ProjectCompilerCodeSyntax.compiled_rename w n b q (old 2)).symm
    (single_at depth tag advance hs s t ih (old 2 w) (old 2 b) (old 2 B) (old 2 z) (old 2 n) (old 2 q)
      (slot 2 0) (slot 2 1) hh hB2 hstep2 (quotes_at 2 ts (old 2 w) (slot 2) 0 hK) (quotes_at 2 ts (old 2 w) (slot 2) 1 hK))

private theorem single_correct (depth tag : Nat) (advance : Bool)
    (hs : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (s t : Tree) (ih : Correct (if advance then depth+1 else depth) s t) :
    Correct depth (.node tag [s]) (.node tag [t]) := by
  intro m Γ w b z n q h
  cases advance
  · exact single_scoped depth tag false hs s t ih w b b z n q h h.scope (by intro he; cases he)
  · let K := (Source.Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) b.castSucc)
    let Δ := Context.add K (Context.image Formula.raise Γ)
    have hb := SyntaxNumerals.range h.zf depth w b h.omega h.scope
    apply Derives.exE (p := K) (.impE (OmegaSyntax.step_at w b (.conjL h.omega)) hb)
    have hK : Derives Δ K := .hyp (Or.inl rfl)
    have hh := h.under K
    have hB := SyntaxNumeralSyntax.intro_succ depth (Fin.last m) b.castSucc hh.scope (.conjR hK)
    exact of_eq (ProjectCompilerCodeSyntax.compiled_rename w n b q Fin.castSucc).symm
      (single_scoped depth tag true hs s t ih w.castSucc b.castSucc (Fin.last m) z.castSucc n.castSucc q.castSucc hh hB (fun _ => .conjR hK))

private theorem binary_correct (depth : Nat) (kind : Fin 4) (s0 s1 t0 t1 : Tree)
    (ih0 : Correct depth s0 t0) (ih1 : Correct depth s1 t1) :
    Correct depth (.node (SyntaxLogicalSyntax.binaryTag kind) [s0,s1]) (.node (SyntaxLogicalSyntax.binaryTag kind) [t0,t1]) := by
  intro m Γ w b z n q h
  let ts : Fin 4 → Tree := fun i => match i.val with | 0 => s0 | 1 => s1 | 2 => t0 | _ => t1
  let K := quoteBody 4 ts w
  let Δ := Context.add K (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 K _ (quote_exists h.zf 4 ts w h.omega)
  have hK : Derives Δ K := .hyp (Or.inl rfl)
  have hh := h.body 4 K
  let ww := old 4 w
  let bb := old 4 b
  let zz := old 4 z
  let nn := old 4 n
  let qq := old 4 q
  let x := slot 4 (m := m) 0
  let y := slot 4 (m := m) 1
  let X := slot 4 (m := m) 2
  let Y := slot 4 (m := m) 3
  have hx : Derives Δ (OriginalTreeQuotationSyntax.tree s0 ww x) := quotes_at 4 ts ww (slot 4) 0 hK
  have hy : Derives Δ (OriginalTreeQuotationSyntax.tree s1 ww y) := quotes_at 4 ts ww (slot 4) 1 hK
  have hX : Derives Δ (OriginalTreeQuotationSyntax.tree t0 ww X) := quotes_at 4 ts ww (slot 4) 2 hK
  have hY : Derives Δ (OriginalTreeQuotationSyntax.tree t1 ww Y) := quotes_at 4 ts ww (slot 4) 3 hK
  have hn := OriginalQuotationNodeFields.tree_to_constructor hh.zf (SyntaxLogicalSyntax.binaryTag kind) [s0,s1] ww nn
    (SyntaxAtomSyntax.two x y) hh.omega (.conjI hx (.conjI hy (.eqRefl ww))) hh.input
  have hq := OriginalQuotationNodeFields.tree_to_constructor hh.zf (SyntaxLogicalSyntax.binaryTag kind) [t0,t1] ww qq
    (SyntaxAtomSyntax.two X Y) hh.omega (.conjI hX (.conjI hY (.eqRefl ww))) hh.output
  have hc0 := ih0 ww bb zz x X ⟨hh.zf,hh.omega,hh.scope,hh.zero,hx,hX⟩
  have hc1 := ih1 ww bb zz y Y ⟨hh.zf,hh.omega,hh.scope,hh.zero,hy,hY⟩
  have hm0 := SyntaxConstructors.child_member hh.zf 2 _ ww (SyntaxAtomSyntax.two x y) nn 0 hh.omega hn
  have hm1 := SyntaxConstructors.child_member hh.zf 2 _ ww (SyntaxAtomSyntax.two x y) nn 1 hh.omega hn
  have hquery0 : Derives Δ (ProjectCompilerCaseSyntax.queried ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters ww) nn x bb X) :=
    .conjI hm0 (of_eq (ProjectCompilerRecursiveSyntax.codeMatrix_at _ x bb X).symm hc0)
  have hquery1 : Derives Δ (ProjectCompilerCaseSyntax.queried ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters ww) nn y bb Y) :=
    .conjI hm1 (of_eq (ProjectCompilerRecursiveSyntax.codeMatrix_at _ y bb Y).symm hc1)
  have hcase := ProjectCompilerCaseIntro.binary_case kind ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters ww)
    ww bb nn qq x y X Y (.conjI hn (.conjI hquery0 (.conjI hquery1 hq)))
  have hc := ProjectCompilerCompleteIntro.of_cases hh.zf ww nn bb qq zz hh.omega
    (OriginalTreeQuotationProperties.tree_range hh.zf _ ww nn hh.omega hh.input)
    (SyntaxNumerals.range hh.zf depth ww bb hh.omega hh.scope)
    (OriginalTreeQuotationProperties.tree_range hh.zf _ ww qq hh.omega hh.output) hh.zero
      (ProjectCompilerCompleteConstructors.binary_cases kind ww bb zz nn qq hcase)
  exact of_eq (ProjectCompilerCodeSyntax.compiled_rename w n b q (old 4)).symm hc

private def variableTree (i : Nat) : Tree := .node 0 [leaf i]
private def memberTree (x y : Tree) : Tree := .node 2 [leaf 0,x,y]
private def subsetTree (i j : Nat) : Tree := .node 9 [.node 7
  [memberTree (variableTree 0) (variableTree (i+1)),memberTree (variableTree 0) (variableTree (j+1))]]

private def atomSource (kind : Fin 3) (i j : Nat) : Tree := .node (ProjectAtomicSyntax.sourceTag kind) [variableTree i,variableTree j]
private def atomTarget (kind : Fin 3) (i j : Nat) : Tree :=
  if kind.val = 0 then memberTree (variableTree i) (variableTree j)
  else if kind.val = 1 then .node 3 [variableTree i,variableTree j] else subsetTree i j

private theorem term_branch {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (depth i : Nat) (hi : i < depth)
    (w b x : Fin m) (hw : Derives Γ (omega w)) (hb : Derives Γ (SyntaxNumeralSyntax.numeral depth b))
    (hx : Derives Γ (OriginalTreeQuotationSyntax.tree (variableTree i) w x)) : Derives Γ (SyntaxTermSyntax.branch true w b x) := by
  let K := (Source.Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral i (Fin.last m))
  let Δ := Context.add K (Context.image Formula.raise Γ)
  apply Derives.exE (p := K) (SyntaxNumerals.exists_numeral hZ i w hw)
  have hK : Derives Δ K := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ K
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw K)
  have hb1 := of_eq (SyntaxNumeralSyntax.numeral_rename depth b Fin.castSucc) (under hb K)
  have hx1 := of_eq (OriginalTreeQuotationSyntax.tree_rename _ w x Fin.castSucc) (under hx K)
  have hc := OriginalQuotationVariableFields.variable_of_tree hZ1 true i w.castSucc (Fin.last m) x.castSucc hw1 (.conjR hK) hx1
  have hl := SyntaxNumerals.less hZ1 i depth hi (Fin.last m) b.castSucc (.conjR hK) hb1
  exact of_eq (SyntaxTermSyntax.branch_rename true w b x Fin.castSucc).symm
    (SyntaxTermSyntax.intro_branch true w.castSucc b.castSucc x.castSucc (Fin.last m) hl hc)

private theorem shift_quotation {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (i : Nat) (w x y : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (OriginalTreeQuotationSyntax.tree (variableTree i) w x))
    (hy : Derives Γ (OriginalTreeQuotationSyntax.tree (variableTree (i+1)) w y)) : Derives Γ (ProjectBoundShiftSyntax.shifted w x y) := by
  let I := (Source.Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral i (Fin.last m))
  let Ξ := Context.add I (Context.image Formula.raise Γ)
  apply Derives.exE (p := I) (SyntaxNumerals.exists_numeral hZ i w hw)
  have hI : Derives Ξ I := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw I)
  let J := (Source.Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (successor (Fin.last (m+1)) (Fin.last m).castSucc)
  let Δ := Context.add J (Context.image Formula.raise Ξ)
  apply Derives.exE (p := J) (.impE (OmegaSyntax.step_at w.castSucc (Fin.last m) (.conjL hw1)) (.conjL hI))
  have hJ : Derives Δ J := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under (ZFContext.under hZ I) J
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise,omega_rename]) (under hw1 J)
  have hi2 := of_eq (SyntaxNumeralSyntax.numeral_rename i (Fin.last m) Fin.castSucc) (under (.conjR hI) J)
  have hj2 := SyntaxNumeralSyntax.intro_succ i (Fin.last (m+1)) (Fin.last m).castSucc hi2 (.conjR hJ)
  have hx2 : Derives Δ (OriginalTreeQuotationSyntax.tree (variableTree i) w.castSucc.castSucc x.castSucc.castSucc) := of_eq (by simp only [Formula.raise,OriginalTreeQuotationSyntax.tree_rename]) (under (under hx I) J)
  have hy2 : Derives Δ (OriginalTreeQuotationSyntax.tree (variableTree (i+1)) w.castSucc.castSucc y.castSucc.castSucc) := of_eq (by simp only [Formula.raise,OriginalTreeQuotationSyntax.tree_rename]) (under (under hy I) J)
  have hc0 := OriginalQuotationVariableFields.variable_of_tree hZ2 true i w.castSucc.castSucc (Fin.last m).castSucc x.castSucc.castSucc hw2 hi2 hx2
  have hc1 := OriginalQuotationVariableFields.variable_of_tree hZ2 true (i+1) w.castSucc.castSucc (Fin.last (m+1)) y.castSucc.castSucc hw2 hj2 hy2
  exact of_eq (by simp only [Formula.raise,ProjectBoundShiftSyntax.shifted_rename])
    (ProjectBoundShiftSyntax.intro_shifted w.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc
      (Fin.last m).castSucc (Fin.last (m+1)) (.conjI hc0 (.conjI (.conjR hJ) hc1)))

private theorem atom_finish {m} {Γ : Context m} (depth : Nat) (kind : Fin 3) (i j : Nat)
    (w b z n q x y : Fin m) (h : Frame Γ depth w b z n q (atomSource kind i j) (atomTarget kind i j))
    (hx : Derives Γ (OriginalTreeQuotationSyntax.tree (variableTree i) w x))
    (hy : Derives Γ (OriginalTreeQuotationSyntax.tree (variableTree j) w y))
    (hxt : Derives Γ (SyntaxTermSyntax.branch true w b x)) (hyt : Derives Γ (SyntaxTermSyntax.branch true w b y))
    (hr : Derives Γ (ProjectAtomicSyntax.result kind w b z x y q)) : Derives Γ (ProjectCompilerCodeSyntax.compiled w n b q) := by
  have hn := OriginalQuotationNodeFields.tree_to_constructor h.zf (ProjectAtomicSyntax.sourceTag kind) [variableTree i,variableTree j]
    w n (SyntaxAtomSyntax.two x y) h.omega (.conjI hx (.conjI hy (.eqRefl w))) h.input
  exact ProjectCompilerBase.atomic_compiled h.zf kind w b z x y n q h.omega h.zero
    (.conjI (.conjI (SyntaxNumerals.range h.zf depth w b h.omega h.scope) (.conjI hxt (.conjI hyt hn))) hr)

private theorem equal_at {m} {Γ : Context m} (depth i j : Nat) (w b z n q x y : Fin m)
    (h : Frame Γ depth w b z n q (atomSource 1 i j) (atomTarget 1 i j))
    (hx : Derives Γ (OriginalTreeQuotationSyntax.tree (variableTree i) w x))
    (hy : Derives Γ (OriginalTreeQuotationSyntax.tree (variableTree j) w y))
    (hxt : Derives Γ (SyntaxTermSyntax.branch true w b x)) (hyt : Derives Γ (SyntaxTermSyntax.branch true w b y)) :
    Derives Γ (ProjectCompilerCodeSyntax.compiled w n b q) := by
  have hq := OriginalQuotationNodeFields.tree_to_constructor h.zf 3 [variableTree i,variableTree j]
    w q (SyntaxAtomSyntax.two x y) h.omega (.conjI hx (.conjI hy (.eqRefl w))) h.output
  exact atom_finish depth 1 i j w b z n q x y h hx hy hxt hyt hq

private theorem member_at {m} {Γ : Context m} (depth i j : Nat) (w b z n q x y : Fin m)
    (h : Frame Γ depth w b z n q (atomSource 0 i j) (atomTarget 0 i j))
    (hx : Derives Γ (OriginalTreeQuotationSyntax.tree (variableTree i) w x))
    (hy : Derives Γ (OriginalTreeQuotationSyntax.tree (variableTree j) w y))
    (hxt : Derives Γ (SyntaxTermSyntax.branch true w b x)) (hyt : Derives Γ (SyntaxTermSyntax.branch true w b y)) :
    Derives Γ (ProjectCompilerCodeSyntax.compiled w n b q) := by
  let K := (Source.Formula.mem (Fin.last m) w.castSucc).conj (OriginalTreeQuotationSyntax.tree (leaf 0) w.castSucc (Fin.last m))
  let Δ := Context.add K (Context.image Formula.raise Γ)
  apply Derives.exE (p := K) (OriginalTreeQuotationExistence.tree_exists h.zf (leaf 0) w h.omega)
  have hK : Derives Δ K := .hyp (Or.inl rfl)
  have hh := h.under K
  have hx1 := of_eq (OriginalTreeQuotationSyntax.tree_rename _ w x Fin.castSucc) (under hx K)
  have hy1 := of_eq (OriginalTreeQuotationSyntax.tree_rename _ w y Fin.castSucc) (under hy K)
  have hs := OriginalQuotationNodeFields.tree_to_constructor hh.zf 0 [] w.castSucc (Fin.last m) Fin.elim0 hh.omega (.eqRefl w.castSucc) (.conjR hK)
  have hq := OriginalQuotationNodeFields.tree_to_constructor hh.zf 2 [leaf 0,variableTree i,variableTree j]
    w.castSucc q.castSucc (SyntaxAtomSyntax.three (Fin.last m) x.castSucc y.castSucc) hh.omega
      (.conjI (.conjR hK) (.conjI hx1 (.conjI hy1 (.eqRefl w.castSucc)))) hh.output
  have hr : Derives Δ (ProjectAtomicSyntax.memberResult w.castSucc x.castSucc y.castSucc q.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate,Formula.rename,SyntaxAtomSyntax.zeroScalar_rename,SyntaxAtomSyntax.memberCode_rename,
      Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]; rfl) (.conjI hs hq)
  exact of_eq (ProjectCompilerCodeSyntax.compiled_rename w n b q Fin.castSucc).symm
    (atom_finish depth 0 i j w.castSucc b.castSucc z.castSucc n.castSucc q.castSucc x.castSucc y.castSucc hh hx1 hy1
      (of_eq (SyntaxTermSyntax.branch_rename true w b x Fin.castSucc) (under hxt K))
      (of_eq (SyntaxTermSyntax.branch_rename true w b y Fin.castSucc) (under hyt K)) hr)

private theorem subset_at {m} {Γ : Context m} (depth i j : Nat) (w b z n q x y : Fin m)
    (h : Frame Γ depth w b z n q (atomSource 2 i j) (atomTarget 2 i j))
    (hx : Derives Γ (OriginalTreeQuotationSyntax.tree (variableTree i) w x))
    (hy : Derives Γ (OriginalTreeQuotationSyntax.tree (variableTree j) w y))
    (hxt : Derives Γ (SyntaxTermSyntax.branch true w b x)) (hyt : Derives Γ (SyntaxTermSyntax.branch true w b y)) :
    Derives Γ (ProjectCompilerCodeSyntax.compiled w n b q) := by
  let B := (Source.Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) b.castSucc)
  let Ξ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (.impE (OmegaSyntax.step_at w b (.conjL h.omega)) (SyntaxNumerals.range h.zf depth w b h.omega h.scope))
  apply of_eq (ProjectCompilerCodeSyntax.compiled_rename w n b q Fin.castSucc).symm
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have h1 := h.under B
  let ts : Fin 7 → Tree := fun k => match k.val with
    | 0 => variableTree (i+1)
    | 1 => variableTree (j+1)
    | 2 => variableTree 0
    | 3 => leaf 0
    | 4 => memberTree (variableTree 0) (variableTree (i+1))
    | 5 => memberTree (variableTree 0) (variableTree (j+1))
    | _ => .node 7 [memberTree (variableTree 0) (variableTree (i+1)),memberTree (variableTree 0) (variableTree (j+1))]
  let K := quoteBody 7 ts w.castSucc
  let Δ := Context.add K (raisedContext 7 Ξ)
  apply HornBinderRules.eliminate_many 7 K _ (quote_exists h1.zf 7 ts w.castSucc h1.omega)
  have hK : Derives Δ K := .hyp (Or.inl rfl)
  have hh := h1.body 7 K
  let r : Fin m → Fin (m+1+7) := fun a => old 7 a.castSucc
  let ww := r w
  let bb := r b
  let zz := r z
  let nn := r n
  let qq := r q
  let s := slot 7 (m := m+1)
  let env : Fin 8 → Fin (m+1+7) := Fin.cases (old 7 (Fin.last m)) s
  have hx8 : Derives Δ (OriginalTreeQuotationSyntax.tree (variableTree i) ww (r x)) :=
    of_eq (by simp only [Formula.raise,OriginalTreeQuotationSyntax.tree_rename]; rfl) (HornBinderRules.under_body 7 (under hx B) K)
  have hy8 : Derives Δ (OriginalTreeQuotationSyntax.tree (variableTree j) ww (r y)) :=
    of_eq (by simp only [Formula.raise,OriginalTreeQuotationSyntax.tree_rename]; rfl) (HornBinderRules.under_body 7 (under hy B) K)
  have q0 : Derives Δ (OriginalTreeQuotationSyntax.tree (variableTree (i+1)) ww (s 0)) := by
    exact of_eq (by rfl) (quotes_at 7 ts ww s 0 hK)
  have q1 : Derives Δ (OriginalTreeQuotationSyntax.tree (variableTree (j+1)) ww (s 1)) := by
    exact of_eq (by rfl) (quotes_at 7 ts ww s 1 hK)
  have q2 : Derives Δ (OriginalTreeQuotationSyntax.tree (variableTree 0) ww (s 2)) := by
    exact of_eq (by rfl) (quotes_at 7 ts ww s 2 hK)
  have q3 : Derives Δ (OriginalTreeQuotationSyntax.tree (leaf 0) ww (s 3)) := by
    exact of_eq (by rfl) (quotes_at 7 ts ww s 3 hK)
  have q4 : Derives Δ (OriginalTreeQuotationSyntax.tree (memberTree (variableTree 0) (variableTree (i+1))) ww (s 4)) := by
    exact of_eq (by rfl) (quotes_at 7 ts ww s 4 hK)
  have q5 : Derives Δ (OriginalTreeQuotationSyntax.tree (memberTree (variableTree 0) (variableTree (j+1))) ww (s 5)) := by
    exact of_eq (by rfl) (quotes_at 7 ts ww s 5 hK)
  have q6 : Derives Δ (OriginalTreeQuotationSyntax.tree (.node 7 [memberTree (variableTree 0) (variableTree (i+1)),memberTree (variableTree 0) (variableTree (j+1))]) ww (s 6)) := by
    exact of_eq (by rfl) (quotes_at 7 ts ww s 6 hK)
  have hs0 := shift_quotation hh.zf i ww (r x) (s 0) hh.omega hx8 q0
  have hs1 := shift_quotation hh.zf j ww (r y) (s 1) hh.omega hy8 q1
  have hv0 := OriginalQuotationVariableFields.variable_of_tree hh.zf true 0 ww zz (s 2) hh.omega hh.zero q2
  have hzero := OriginalQuotationNodeFields.tree_to_constructor hh.zf 0 [] ww (s 3) Fin.elim0 hh.omega (.eqRefl ww) q3
  have hm0 := OriginalQuotationNodeFields.tree_to_constructor hh.zf 2 [leaf 0,variableTree 0,variableTree (i+1)] ww (s 4)
    (SyntaxAtomSyntax.three (s 3) (s 2) (s 0)) hh.omega
      (by simpa only [OriginalQuotationFieldSyntax.fields,SyntaxAtomSyntax.three,SyntaxAtomSyntax.two,Fin.cases_zero,Fin.cases_succ] using Derives.conjI q3 (.conjI q2 (.conjI q0 (.eqRefl ww)))) q4
  have hm1 := OriginalQuotationNodeFields.tree_to_constructor hh.zf 2 [leaf 0,variableTree 0,variableTree (j+1)] ww (s 5)
    (SyntaxAtomSyntax.three (s 3) (s 2) (s 1)) hh.omega
      (by simpa only [OriginalQuotationFieldSyntax.fields,SyntaxAtomSyntax.three,SyntaxAtomSyntax.two,Fin.cases_zero,Fin.cases_succ] using Derives.conjI q3 (.conjI q2 (.conjI q1 (.eqRefl ww)))) q5
  have himp := OriginalQuotationNodeFields.tree_to_constructor hh.zf 7
    [memberTree (variableTree 0) (variableTree (i+1)),memberTree (variableTree 0) (variableTree (j+1))] ww (s 6)
    (SyntaxAtomSyntax.two (s 4) (s 5)) hh.omega (by simpa only [OriginalQuotationFieldSyntax.fields,SyntaxAtomSyntax.two,Fin.cases_zero,Fin.cases_succ] using Derives.conjI q4 (.conjI q5 (.eqRefl ww))) q6
  have hall := OriginalQuotationNodeFields.tree_to_constructor hh.zf 9
    [.node 7 [memberTree (variableTree 0) (variableTree (i+1)),memberTree (variableTree 0) (variableTree (j+1))]] ww qq
    (fun _ => s 6) hh.omega (.conjI q6 (.eqRefl ww)) hh.output
  have hsucc : Derives Δ (successor (old 7 (Fin.last m)) bb) :=
    of_eq (successor_rename (Fin.last m) b.castSucc (old 7)) (HornBinderRules.under_body 7 (.conjR hB) K)
  have hmatrix : Derives Δ (ProjectSubsetSyntax.matrix ww bb zz (r x) (r y) qq env) :=
    .conjI hsucc (.conjI hs0 (.conjI hs1 (.conjI hv0 (.conjI hzero (.conjI hm0 (.conjI hm1 (.conjI himp hall)))))))
  have hr := ProjectSubsetSyntax.intro_expanded ww bb zz (r x) (r y) qq env hmatrix
  have hxt8 : Derives Δ (SyntaxTermSyntax.branch true ww bb (r x)) := of_eq (by simp only [Formula.raise,SyntaxTermSyntax.branch_rename]; rfl) (HornBinderRules.under_body 7 (under hxt B) K)
  have hyt8 : Derives Δ (SyntaxTermSyntax.branch true ww bb (r y)) := of_eq (by simp only [Formula.raise,SyntaxTermSyntax.branch_rename]; rfl) (HornBinderRules.under_body 7 (under hyt B) K)
  exact of_eq (ProjectCompilerCodeSyntax.compiled_rename w.castSucc n.castSucc b.castSucc q.castSucc (old 7)).symm
    (atom_finish depth 2 i j ww bb zz nn qq (r x) (r y) hh hx8 hy8 hxt8 hyt8 hr)

private theorem atomic_correct (depth : Nat) (kind : Fin 3) (i j : Nat) (hi : i < depth) (hj : j < depth) :
    Correct depth (atomSource kind i j) (atomTarget kind i j) := by
  intro m Γ w b z n q h
  let ts : Fin 2 → Tree := Fin.cases (variableTree i) (fun _ => variableTree j)
  let K := quoteBody 2 ts w
  let Δ := Context.add K (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 K _ (quote_exists h.zf 2 ts w h.omega)
  have hK : Derives Δ K := .hyp (Or.inl rfl)
  have hh := h.body 2 K
  let ww := old 2 w
  let bb := old 2 b
  let zz := old 2 z
  let nn := old 2 n
  let qq := old 2 q
  let x := slot 2 (m := m) 0
  let y := slot 2 (m := m) 1
  have hx : Derives Δ (OriginalTreeQuotationSyntax.tree (variableTree i) ww x) := quotes_at 2 ts ww (slot 2) 0 hK
  have hy : Derives Δ (OriginalTreeQuotationSyntax.tree (variableTree j) ww y) := quotes_at 2 ts ww (slot 2) 1 hK
  have hxt := term_branch hh.zf depth i hi ww bb x hh.omega hh.scope hx
  have hyt := term_branch hh.zf depth j hj ww bb y hh.omega hh.scope hy
  apply of_eq (ProjectCompilerCodeSyntax.compiled_rename w n b q (old 2)).symm
  rcases kind with ⟨k,hk⟩
  have hc : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hc with rfl | rfl | rfl
  · exact member_at depth i j ww bb zz nn qq x y hh hx hy hxt hyt
  · exact equal_at depth i j ww bb zz nn qq x y hh hx hy hxt hyt
  · exact subset_at depth i j ww bb zz nn qq x y hh hx hy hxt hyt

private theorem bound_index {depth : Nat} (i : Fin depth) :
    (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_variable i).index = i.val := by
  induction depth with
  | zero => exact Fin.elim0 i
  | succ depth ih =>
    refine Fin.cases rfl (fun j => ?_) i
    exact congrArg Nat.succ (ih j)

open YesMetaZFC.SetTheory.Definitional.Project (fo_formula fo_term fo_mem)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC

private theorem term_tree {depth : Nat} (input : YesMetaZFC.SetTheory.Definitional.Project.Term depth) (hc : input.freeSupport = []) :
    PureSyntaxQuotation.termTree (fo_term input hc) = ProjectEncode.term input := by
  cases input with
  | bound i =>
    change Tree.node 0 [leaf (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_variable i).index] = Tree.node 0 [leaf i.val]
    rw [bound_index]
  | free id => cases hc

private theorem term_weaken_tree {depth : Nat} (input : YesMetaZFC.SetTheory.Definitional.Project.Term depth) (hc : input.freeSupport = []) :
    PureSyntaxQuotation.termTree ((fo_term input hc).weakenBound YesMetaZFC.SetTheory.SetSort.set) =
      (match input with | .bound i => variableTree (i.val+1) | .free _ => leaf 0) := by
  cases input with
  | bound i =>
    change Tree.node 0 [leaf ((YesMetaZFC.SetTheory.Definitional.Project.fo_bound_variable i).index+1)] = variableTree (i.val+1)
    rw [bound_index]
    rfl
  | free id => cases hc

attribute [local irreducible] Correct

private theorem original_correct {depth : Nat} (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 depth)
    (hc : input.FreeClosed) : Correct depth (ProjectEncode.formula input) (PureSyntaxQuotation.formulaTree (fo_formula input hc)) := by
  revert hc
  induction input with
  | falsum => intro hc; exact Eq.mp (by simp -implicitDefEqProofs only [Correct,Bool.false_eq_true,PureSyntaxQuotation.Original.leaf,ProjectEncode.formula,fo_formula,PureSyntaxQuotation.formulaTree,PureSyntaxQuotation.Original.leaf,SyntaxAtomSyntax.nullaryTag,↓reduceIte] <;> rfl) (@constant_correct _ false)
  | truth => intro hc; exact Eq.mp (by simp -implicitDefEqProofs only [Correct,PureSyntaxQuotation.Original.leaf,ProjectEncode.formula,fo_formula,PureSyntaxQuotation.formulaTree,PureSyntaxQuotation.Original.leaf,SyntaxAtomSyntax.nullaryTag,↓reduceIte] <;> rfl) (@constant_correct _ true)
  | mem left right =>
    intro hc
    simp only [YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hc
    cases left with
    | free id => cases hc.1
    | bound i =>
      cases right with
      | free id => cases hc.2
      | bound j =>
        exact Eq.mp (by simp -implicitDefEqProofs only [Correct,Fin.isValue,PureSyntaxQuotation.Original.leaf,ProjectEncode.formula,ProjectEncode.term,fo_formula,fo_mem,term_tree,
          PureSyntaxQuotation.formulaTree,PureSyntaxQuotation.argumentTrees,
          atomSource,atomTarget,memberTree,variableTree,ProjectAtomicSyntax.sourceTag] <;> rfl) (@atomic_correct _ 0 i.val j.val i.isLt j.isLt)
  | atom symbol stage args =>
    intro hc
    simp only [YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed,YesMetaZFC.SetTheory.Definitional.TermVector.FreeClosed] at hc
    have h0 := hc 0
    have h1 := hc 1
    cases hL : args 0 with
    | free id => rw [hL] at h0; cases h0
    | bound i =>
      cases hR : args 1 with
      | free id => rw [hR] at h1; cases h1
      | bound j =>
        cases symbol
        · exact Eq.mp (by simp -implicitDefEqProofs only [Correct,Fin.isValue,ProjectEncode.formula,ProjectEncode.term,fo_formula,PureSyntaxQuotation.formulaTree,term_tree,hL,hR,
            PureSyntaxQuotation.formulaTree,
            atomSource,atomTarget,variableTree,ProjectAtomicSyntax.sourceTag] <;> rfl) (@atomic_correct _ 1 i.val j.val i.isLt j.isLt)
        · exact Eq.mp (by simp -implicitDefEqProofs only [Correct,Fin.isValue,PureSyntaxQuotation.Original.leaf,ProjectEncode.formula,ProjectEncode.term,fo_formula,fo_mem,PureSyntaxQuotation.formulaTree,PureSyntaxQuotation.argumentTrees,term_weaken_tree,hL,hR,
            PureSyntaxQuotation.formulaTree,PureSyntaxQuotation.argumentTrees,




            atomSource,atomTarget,subsetTree,memberTree,variableTree,ProjectAtomicSyntax.sourceTag] <;> rfl) (@atomic_correct _ 2 i.val j.val i.isLt j.isLt)
  | neg body ih =>
    intro hc
    simp only [YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hc
    exact Eq.mp (by simp -implicitDefEqProofs only [Correct,ProjectEncode.formula,fo_formula,PureSyntaxQuotation.formulaTree] <;> rfl) (@single_correct _ 4 false (Or.inl ⟨rfl,rfl⟩) _ _ (@ih hc))
  | conj left right ihL ihR =>
    intro hc
    simp only [YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hc
    exact Eq.mp (by simp -implicitDefEqProofs only [Correct,ProjectEncode.formula,fo_formula,PureSyntaxQuotation.formulaTree,SyntaxLogicalSyntax.binaryTag,Fin.isValue] <;> rfl) (@binary_correct _ 0 _ _ _ _ (@ihL hc.1) (@ihR hc.2))
  | disj left right ihL ihR =>
    intro hc
    simp only [YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hc
    exact Eq.mp (by simp -implicitDefEqProofs only [Correct,ProjectEncode.formula,fo_formula,PureSyntaxQuotation.formulaTree,SyntaxLogicalSyntax.binaryTag,Fin.isValue] <;> rfl) (@binary_correct _ 1 _ _ _ _ (@ihL hc.1) (@ihR hc.2))
  | imp left right ihL ihR =>
    intro hc
    simp only [YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hc
    exact Eq.mp (by simp -implicitDefEqProofs only [Correct,ProjectEncode.formula,fo_formula,PureSyntaxQuotation.formulaTree,SyntaxLogicalSyntax.binaryTag,Fin.isValue] <;> rfl) (@binary_correct _ 2 _ _ _ _ (@ihL hc.1) (@ihR hc.2))
  | iff left right ihL ihR =>
    intro hc
    simp only [YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hc
    exact Eq.mp (by simp -implicitDefEqProofs only [Correct,ProjectEncode.formula,fo_formula,PureSyntaxQuotation.formulaTree,SyntaxLogicalSyntax.binaryTag,Fin.isValue] <;> rfl) (@binary_correct _ 3 _ _ _ _ (@ihL hc.1) (@ihR hc.2))
  | forallE body ih =>
    intro hc
    simp only [YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hc
    exact Eq.mp (by simp -implicitDefEqProofs only [Correct,ProjectEncode.formula,fo_formula,PureSyntaxQuotation.formulaTree] <;> rfl) (@single_correct _ 9 true (Or.inr (Or.inl ⟨rfl,rfl⟩)) _ _ (@ih hc))
  | existsE body ih =>
    intro hc
    simp only [YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hc
    exact Eq.mp (by simp -implicitDefEqProofs only [Correct,ProjectEncode.formula,fo_formula,PureSyntaxQuotation.formulaTree] <;> rfl) (@single_correct _ 10 true (Or.inr (Or.inr ⟨rfl,rfl⟩)) _ _ (@ih hc))

attribute [local semireducible] Correct

/-- Every ORIGINAL Project body, all twelve constructors, and arbitrary
internal input/output candidates. External syntax indexes the proof scheme. -/
theorem construct {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {depth : Nat}
    (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 depth) (hc : input.FreeClosed)
    (w b z n q : Fin m) (hw : Derives Γ (omega w)) (hb : Derives Γ (SyntaxNumeralSyntax.numeral depth b))
    (hz : Derives Γ (empty z)) (hn : Derives Γ (OriginalTreeQuotationSyntax.tree (ProjectEncode.formula input) w n))
    (hq : Derives Γ (PureQuotationSyntax.formula (fo_formula input hc) w q)) :
    Derives Γ (ProjectCompilerCodeSyntax.compiled w n b q) :=
  original_correct input hc w b z n q ⟨hZ,hw,hb,hz,hn,hq⟩

theorem formula_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {depth : Nat}
    (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 depth) (hc : input.FreeClosed)
    (w b z n q : Fin m) (hw : Derives Γ (omega w)) (hb : Derives Γ (SyntaxNumeralSyntax.numeral depth b))
    (hz : Derives Γ (empty z)) (hn : Derives Γ (OriginalTreeQuotationSyntax.tree (ProjectEncode.formula input) w n)) :
    Derives Γ ((ProjectCompilerCodeSyntax.compiled w n b q).iff (PureQuotationSyntax.formula (fo_formula input hc) w q)) := by
  have he := OriginalTreeQuotationExistence.tree_exists hZ (PureSyntaxQuotation.formulaTree (fo_formula input hc)) w hw
  apply Derives.conjI
  · apply Derives.impI
    let E := ProjectCompilerCodeSyntax.compiled w n b q
    let Ξ := Context.add E Γ
    let P := (Source.Formula.mem (Fin.last m) w.castSucc).conj (PureQuotationSyntax.formula (fo_formula input hc) w.castSucc (Fin.last m))
    let Δ := Context.add P (Context.image Formula.raise Ξ)
    apply Derives.exE (p := P) (add he E)
    have hP : Derives Δ P := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ E) P
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw E) P)
    have hb1 := of_eq (SyntaxNumeralSyntax.numeral_rename depth b Fin.castSucc) (under (add hb E) P)
    have hz1 := of_eq (empty_rename z Fin.castSucc) (under (add hz E) P)
    have hn1 := of_eq (OriginalTreeQuotationSyntax.tree_rename _ w n Fin.castSucc) (under (add hn E) P)
    have hC := construct hZ1 input hc w.castSucc b.castSucc z.castSucc n.castSucc (Fin.last m) hw1 hb1 hz1 hn1 (.conjR hP)
    have hE : Derives Ξ E := .hyp (Or.inl rfl)
    have hE1 := of_eq (ProjectCompilerCodeSyntax.compiled_rename w n b q Fin.castSucc) (under hE P)
    have hEq := ProjectCompilerUnique.unique_outputs hZ1 w.castSucc n.castSucc b.castSucc (Fin.last m) q.castSucc hw1 hC hE1
    have ho := OriginalQuotationValue.tree_output_subst (PureSyntaxQuotation.formulaTree (fo_formula input hc))
      w.castSucc (Fin.last m) q.castSucc hEq (.conjR hP)
    exact of_eq (PureQuotationSyntax.formula_rename (fo_formula input hc) w q Fin.castSucc).symm ho
  · apply Derives.impI
    exact construct (ZFContext.add hZ _) input hc w b z n q (add hw _) (add hb _) (add hz _) (add hn _) (.hyp (Or.inl rfl))

def sentence {m} {depth : Nat} (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 depth) (hc : input.FreeClosed)
    (w b z n q : Fin m) : Source.Sentence :=
  ((omega w).imp ((SyntaxNumeralSyntax.numeral depth b).imp ((empty z).imp
    ((OriginalTreeQuotationSyntax.tree (ProjectEncode.formula input) w n).imp
      ((ProjectCompilerCodeSyntax.compiled w n b q).iff (PureQuotationSyntax.formula (fo_formula input hc) w q)))))).close

theorem source_certificate {m} {depth : Nat} (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 depth) (hc : input.FreeClosed)
    (w b z n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (sentence input hc w b z n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ := Context.add (OriginalTreeQuotationSyntax.tree (ProjectEncode.formula input) w n)
    (Context.add (empty z) (Context.add (SyntaxNumeralSyntax.numeral depth b) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _
  exact formula_iff hZ input hc w b z n q (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem kernel_certificate {m} {depth : Nat} (input : YesMetaZFC.SetTheory.Definitional.Project.Formula 1 depth) (hc : input.FreeClosed)
    (w b z n q : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence input hc w b z n q)) :=
  ZFReplay.replay (TheoryTransport.sentence (source_certificate input hc w b z n q))

end PPAC.Migration.ProjectCompilerQuotation
