import PPAC.Migration.ForcingMixedTermLift
import PPAC.Migration.ForcingRebindOpeningTriangle
import PPAC.Migration.Internal.InstantiateTopTermOperation
import PPAC.Migration.Internal.OriginalUniversalBlock
import PPAC.Migration.Internal.SyntaxCodedMixedTermExistence
import PPAC.Migration.Internal.SyntaxRenameTermUnique

/-! The four-table term diagram (three actual coded substitutions versus
one direct substitution) is preserved by ORIGINAL mixed binder advances.
All auxiliary shift/identity maps and old-run witnesses are object witnesses.
This is the binder invariant for full formula cancellation, not final Con. -/
namespace PPAC.Migration.ForcingTermDiagram
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxCodedMixedTermSyntax (substituted substituted_rename)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def src : Fin 4 → Fin 4 := Fin.cases 0 (Fin.cases 1 (Fin.cases 2 (fun _ => 0)))
private def dst : Fin 4 → Fin 4 := Fin.cases 1 (Fin.cases 2 (Fin.cases 3 (fun _ => 3)))

def step {m} (w : Fin m) (a b R S : Fin 4 → Fin m) (edge : Fin 4) (x y : Fin m) : Formula m :=
  substituted w (R edge) (S edge) (a (src edge)) (b (src edge)) (a (dst edge)) (b (dst edge)) x y

theorem step_rename {m l} (w : Fin m) (a b R S : Fin 4 → Fin m) (edge : Fin 4) (x y : Fin m) (r : Fin m → Fin l) :
    (step w a b R S edge x y).rename r = step (r w) (fun i => r (a i)) (fun i => r (b i)) (fun i => r (R i)) (fun i => r (S i)) edge (r x) (r y) := by
  simp only [step, substituted_rename]

private def runs {m} (w : Fin m) (a b R S : Fin 4 → Fin m) (x u t y o : Fin m) : Formula m :=
  (step w a b R S 0 x u).conj ((step w a b R S 1 u t).conj ((step w a b R S 2 t y).conj (step w a b R S 3 x o)))
private theorem runs_rename {m l} (w : Fin m) (a b R S : Fin 4 → Fin m) (x u t y o : Fin m) (r : Fin m → Fin l) :
    (runs w a b R S x u t y o).rename r = runs (r w) (fun i => r (a i)) (fun i => r (b i)) (fun i => r (R i)) (fun i => r (S i)) (r x) (r u) (r t) (r y) (r o) := by
  simp only [runs, Formula.rename, step_rename]
private def point {m} (w : Fin m) (a b R S : Fin 4 → Fin m) (x u t y o : Fin m) : Formula m :=
  (runs w a b R S x u t y o).imp (.equal y o)
private theorem point_rename {m l} (w : Fin m) (a b R S : Fin 4 → Fin m) (x u t y o : Fin m) (r : Fin m → Fin l) :
    (point w a b R S x u t y o).rename r = point (r w) (fun i => r (a i)) (fun i => r (b i)) (fun i => r (R i)) (fun i => r (S i)) (r x) (r u) (r t) (r y) (r o) := by
  simp only [point, Formula.rename, runs_rename]
private def diagramBody {m} (w : Fin m) (a b R S : Fin 4 → Fin m) : Formula (m+5) :=
  point (old 5 w) (fun i => old 5 (a i)) (fun i => old 5 (b i)) (fun i => old 5 (R i)) (fun i => old 5 (S i))
    (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) (slot 5 4)

/-- All five term-code candidates are quantified in the OBJECT theory. -/
def diagram {m} (w : Fin m) (a b R S : Fin 4 → Fin m) : Formula m :=
  OriginalUniversalBlock.allMany 5 (diagramBody w a b R S)

theorem diagram_rename {m l} (w : Fin m) (a b R S : Fin 4 → Fin m) (r : Fin m → Fin l) :
    (diagram w a b R S).rename r = diagram (r w) (fun i => r (a i)) (fun i => r (b i)) (fun i => r (R i)) (fun i => r (S i)) := by
  simp only [diagram, OriginalUniversalBlock.allMany_rename, diagramBody, point_rename, lift_old, lift_slot]

theorem apply_diagram {m} {Γ : Context m} (w : Fin m) (a b R S : Fin 4 → Fin m) (x u t y o : Fin m)
    (hd : Derives Γ (diagram w a b R S))
    (h0 : Derives Γ (step w a b R S 0 x u)) (h1 : Derives Γ (step w a b R S 1 u t))
    (h2 : Derives Γ (step w a b R S 2 t y)) (h3 : Derives Γ (step w a b R S 3 x o)) : Derives Γ (.equal y o) := by
  have hp : Derives Γ (point w a b R S x u t y o) := of_eq
    (by simp only [diagramBody, point_rename, assign_old, assign_slot]; rfl)
    (OriginalUniversalBlock.at_many 5 _ (HornRowFields.five x u t y o) hd)
  exact .impE hp (.conjI h0 (.conjI h1 (.conjI h2 h3)))

private def liftAt {m} (w : Fin m) (a b A R S K H : Fin 4 → Fin m) (e : Fin 4) : Formula m :=
  SyntaxCodedMixedBinderSyntax.lifted w (R e) (S e) (a (src e)) (b (src e)) (a (dst e)) (b (dst e)) (A (src e)) (A (dst e)) (K e) (H e)
private theorem liftAt_rename {m l} (w : Fin m) (a b A R S K H : Fin 4 → Fin m) (e : Fin 4) (r : Fin m → Fin l) :
    (liftAt w a b A R S K H e).rename r = liftAt (r w) (fun i => r (a i)) (fun i => r (b i)) (fun i => r (A i))
      (fun i => r (R i)) (fun i => r (S i)) (fun i => r (K i)) (fun i => r (H i)) e := by
  simp only [liftAt, SyntaxCodedMixedBinderSyntax.lifted_rename]

private structure Basic {m} (Γ : Context m) (w : Fin m) (a b A R S K H : Fin 4 → Fin m) : Prop where
  zf : ZFContext.Evidence Γ
  omega : Derives Γ (omega w)
  oldDiagram : Derives Γ (diagram w a b R S)
  lifts : ∀ e : Fin 4, Derives Γ (liftAt w a b A R S K H e)
private structure Maps {m} (Γ : Context m) (w : Fin m) (a b A U V : Fin 4 → Fin m) : Prop where
  shifts : ∀ i : Fin 4, Derives Γ (SyntaxFreeShiftSyntax.shiftMap w (a i) (A i) (U i))
  identities : ∀ i : Fin 4, Derives Γ (SyntaxIdentityMapSyntax.identityMap w (b i) (V i))
private structure Path {m} (Γ : Context m) (w : Fin m) (A b K H : Fin 4 → Fin m) (X I J Y O : Fin m) : Prop where
  first : Derives Γ (step w A b K H 0 X I)
  second : Derives Γ (step w A b K H 1 I J)
  third : Derives Γ (step w A b K H 2 J Y)
  direct : Derives Γ (step w A b K H 3 X O)

private theorem Basic.add {m} {Γ : Context m} {w : Fin m} {a b A R S K H : Fin 4 → Fin m}
    (h : Basic Γ w a b A R S K H) (E : Formula m) : Basic (Context.add E Γ) w a b A R S K H := {
  zf := ZFContext.add h.zf E
  omega := SourceLogic.add h.omega E
  oldDiagram := SourceLogic.add h.oldDiagram E
  lifts := fun e => SourceLogic.add (h.lifts e) E
}

private theorem Basic.under {m} {Γ : Context m} {w : Fin m} {a b A R S K H : Fin 4 → Fin m}
    (h : Basic Γ w a b A R S K H) (E : Formula (m+1)) : Basic (Context.add E (Context.image Formula.raise Γ)) w.castSucc (fun i => (a i).castSucc) (fun i => (b i).castSucc) (fun i => (A i).castSucc) (fun i => (R i).castSucc) (fun i => (S i).castSucc) (fun i => (K i).castSucc) (fun i => (H i).castSucc) := {
  zf := ZFContext.under h.zf E
  omega := of_eq (omega_rename w Fin.castSucc) (SourceLogic.under h.omega E)
  oldDiagram := of_eq (diagram_rename w a b R S Fin.castSucc) (SourceLogic.under h.oldDiagram E)
  lifts := fun e => of_eq (liftAt_rename w a b A R S K H e Fin.castSucc) (SourceLogic.under (h.lifts e) E)
}

private theorem Maps.add {m} {Γ : Context m} {w : Fin m} {a b A U V : Fin 4 → Fin m}
    (h : Maps Γ w a b A U V) (E : Formula m) : Maps (Context.add E Γ) w a b A U V := {
  shifts := fun i => SourceLogic.add (h.shifts i) E
  identities := fun i => SourceLogic.add (h.identities i) E
}

private theorem Maps.under {m} {Γ : Context m} {w : Fin m} {a b A U V : Fin 4 → Fin m}
    (h : Maps Γ w a b A U V) (E : Formula (m+1)) : Maps (Context.add E (Context.image Formula.raise Γ)) w.castSucc (fun i => (a i).castSucc) (fun i => (b i).castSucc) (fun i => (A i).castSucc) (fun i => (U i).castSucc) (fun i => (V i).castSucc) := {
  shifts := fun i => of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w (a i) (A i) (U i) Fin.castSucc) (SourceLogic.under (h.shifts i) E)
  identities := fun i => of_eq (SyntaxIdentityMapSyntax.identityMap_rename w (b i) (V i) Fin.castSucc) (SourceLogic.under (h.identities i) E)
}

private theorem Path.add {m} {Γ : Context m} {w : Fin m} {A b K H : Fin 4 → Fin m} {X I J Y O : Fin m}
    (h : Path Γ w A b K H X I J Y O) (E : Formula m) : Path (Context.add E Γ) w A b K H X I J Y O := {
  first := SourceLogic.add h.first E
  second := SourceLogic.add h.second E
  third := SourceLogic.add h.third E
  direct := SourceLogic.add h.direct E
}

private theorem Path.under {m} {Γ : Context m} {w : Fin m} {A b K H : Fin 4 → Fin m} {X I J Y O : Fin m}
    (h : Path Γ w A b K H X I J Y O) (E : Formula (m+1)) : Path (Context.add E (Context.image Formula.raise Γ)) w.castSucc (fun i => (A i).castSucc) (fun i => (b i).castSucc) (fun i => (K i).castSucc) (fun i => (H i).castSucc) X.castSucc I.castSucc J.castSucc Y.castSucc O.castSucc := {
  first := of_eq (step_rename w A b K H 0 X I Fin.castSucc) (SourceLogic.under h.first E)
  second := of_eq (step_rename w A b K H 1 I J Fin.castSucc) (SourceLogic.under h.second E)
  third := of_eq (step_rename w A b K H 2 J Y Fin.castSucc) (SourceLogic.under h.third E)
  direct := of_eq (step_rename w A b K H 3 X O Fin.castSucc) (SourceLogic.under h.direct E)
}

private theorem input_lists {m} {Γ : Context m} {w : Fin m} {a b A R S K H : Fin 4 → Fin m}
    (h : Basic Γ w a b A R S K H) (e : Fin 4) :
    Derives Γ (SyntaxMixedImageCodeSyntax.termLists w (a (src e)) (b (src e)) (a (dst e)) (b (dst e)) (R e) (S e)) :=
  SyntaxCodedMixedBinderTyping.input_lists _ _ _ _ _ _ _ _ _ _ _ (h.lifts e)
private theorem output_lists {m} {Γ : Context m} {w : Fin m} {a b A R S K H : Fin 4 → Fin m}
    (h : Basic Γ w a b A R S K H) (e : Fin 4) :
    Derives Γ (SyntaxMixedImageCodeSyntax.termLists w (A (src e)) (b (src e)) (A (dst e)) (b (dst e)) (K e) (H e)) :=
  SyntaxCodedMixedBinderTyping.output_lists _ _ _ _ _ _ _ _ _ _ _ (h.lifts e)

private theorem node_spec {m} {Γ : Context m} {w : Fin m} {a b A R S K H : Fin 4 → Fin m}
    (h : Basic Γ w a b A R S K H) (i : Fin 4) :
    Derives Γ ((Formula.mem (a i) w).conj ((Formula.mem (b i) w).conj (successor (A i) (a i)))) := by
  have source (e : Fin 4) := Derives.conjL (SyntaxCodedMixedBinderTyping.input_of_lifted _ _ _ _ _ _ _ _ _ _ _ (h.lifts e))
  have hs (e : Fin 4) := Derives.conjR (SyntaxCodedMixedBinderTyping.input_of_lifted _ _ _ _ _ _ _ _ _ _ _ (h.lifts e))
  have sourceSpec (e : Fin 4) : Derives Γ ((Formula.mem (a (src e)) w).conj ((Formula.mem (b (src e)) w).conj (successor (A (src e)) (a (src e))))) :=
    .conjI (.conjL (.conjL (source e))) (.conjI (.conjL (.conjR (source e))) (.conjL (hs e)))
  have targetSpec : Derives Γ ((Formula.mem (a 3) w).conj ((Formula.mem (b 3) w).conj (successor (A 3) (a 3)))) :=
    .conjI (.conjL (.conjL (.conjR (.conjL (source 2))))) (.conjI (.conjR (.conjL (.conjR (.conjL (source 2))))) (.conjR (hs 2)))
  exact Fin.cases (sourceSpec 0) (Fin.cases (sourceSpec 1) (Fin.cases (sourceSpec 2) (Fin.cases targetSpec (fun z => Fin.elim0 z)))) i

private theorem rename_input {m} {Γ : Context m} (w r s a b A x y X : Fin m)
    (he : Derives Γ (.equal x y)) (hr : Derives Γ (SyntaxRenameTermSyntax.renamed w r s a b A b x X)) :
    Derives Γ (SyntaxRenameTermSyntax.renamed w r s a b A b y X) := by
  let F := SyntaxRenameTermSyntax.renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc A.castSucc b.castSucc (Fin.last m) X.castSucc
  have hi : Derives Γ (F.instantiate x) := of_eq (by simp only [F, Formula.instantiate, SyntaxRenameTermSyntax.renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hr
  exact of_eq (by simp only [F, Formula.instantiate, SyntaxRenameTermSyntax.renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.eqSubst F he hi)

private theorem at_old_path {m} {Γ : Context m} {w X I J Y O : Fin m} {a b A R S K H U V : Fin 4 → Fin m}
    (h : Basic Γ w a b A R S K H) (maps : Maps Γ w a b A U V) (path : Path Γ w A b K H X I J Y O)
    (x u t y o : Fin m) (hr : Derives Γ (SyntaxRenameTermSyntax.renamed w (U 0) (V 0) (a 0) (b 0) (A 0) (b 0) x X))
    (h0 : Derives Γ (step w a b R S 0 x u)) (h1 : Derives Γ (step w a b R S 1 u t))
    (h2 : Derives Γ (step w a b R S 2 t y)) (h3 : Derives Γ (step w a b R S 3 x o)) : Derives Γ (.equal Y O) := by
  have nr (e : Fin 4) (x q X Y : Fin m) (ho : Derives Γ (step w a b R S e x q))
      (hx : Derives Γ (SyntaxRenameTermSyntax.renamed w (U (src e)) (V (src e)) (a (src e)) (b (src e)) (A (src e)) (b (src e)) x X)) :=
    ForcingMixedTermLift.natural h.zf w (R e) (S e) (a (src e)) (b (src e)) (a (dst e)) (b (dst e)) (A (src e)) (A (dst e)) (K e) (H e)
      (U (dst e)) (V (dst e)) (U (src e)) (V (src e)) x q X Y h.omega (h.lifts e)
      (maps.shifts (src e)) (maps.identities (src e)) (maps.shifts (dst e)) (maps.identities (dst e)) ho hx
  have r1 := Derives.impE (.conjL (nr 0 x u X I h0 hr)) path.first
  have r2 := Derives.impE (.conjL (nr 1 u t I J h1 r1)) path.second
  have r3 := Derives.impE (.conjL (nr 2 t y J Y h2 r2)) path.third
  have r4 := Derives.impE (.conjL (nr 3 x o X O h3 hr)) path.direct
  have he := apply_diagram w a b R S x u t y o h.oldDiagram h0 h1 h2 h3
  exact SyntaxRenameTermUnique.unique h.zf w (U 3) (V 3) (a 3) (b 3) (A 3) (b 3) o Y O h.omega
    (rename_input w (U 3) (V 3) (a 3) (b 3) (A 3) y o Y he r3) r4

private theorem from_old_source {m} {Γ : Context m} {w X I J Y O : Fin m} {a b A R S K H U V : Fin 4 → Fin m}
    (h : Basic Γ w a b A R S K H) (maps : Maps Γ w a b A U V) (path : Path Γ w A b K H X I J Y O)
    (x : Fin m) (hr : Derives Γ (SyntaxRenameTermSyntax.renamed w (U 0) (V 0) (a 0) (b 0) (A 0) (b 0) x X)) :
    Derives Γ (.equal Y O) := by
  have ht := SyntaxRenameTermTyping.source_term w (U 0) (V 0) (a 0) (b 0) (A 0) (b 0) x X hr
  let E0 := step w.castSucc (fun i => (a i).castSucc) (fun i => (b i).castSucc) (fun i => (R i).castSucc) (fun i => (S i).castSucc) 0 x.castSucc (Fin.last m)
  let Γ1 := Context.add E0 (Context.image Formula.raise Γ)
  apply Derives.exE (p := E0) (SyntaxCodedMixedTermExistence.exists_output h.zf w (R 0) (S 0) (a 0) (b 0) (a 1) (b 1) x h.omega (.conjI (input_lists h 0) ht))
  have hE0 : Derives Γ1 E0 := .hyp (Or.inl rfl)
  have h1 := h.under E0
  have maps1 := maps.under E0
  have path1 := path.under E0
  have ht1 := SyntaxCodedMixedTermTyping.target_type w.castSucc (R 0).castSucc (S 0).castSucc (a 0).castSucc (b 0).castSucc (a 1).castSucc (b 1).castSucc x.castSucc (Fin.last m) hE0
  let E1 := step w.castSucc.castSucc (fun i => (a i).castSucc.castSucc) (fun i => (b i).castSucc.castSucc) (fun i => (R i).castSucc.castSucc) (fun i => (S i).castSucc.castSucc) 1 (Fin.last m).castSucc (Fin.last (m+1))
  let Γ2 := Context.add E1 (Context.image Formula.raise Γ1)
  apply Derives.exE (p := E1) (SyntaxCodedMixedTermExistence.exists_output h1.zf w.castSucc (R 1).castSucc (S 1).castSucc (a 1).castSucc (b 1).castSucc (a 2).castSucc (b 2).castSucc (Fin.last m) h1.omega (.conjI (input_lists h1 1) ht1))
  have hE1 : Derives Γ2 E1 := .hyp (Or.inl rfl)
  have h2 := h1.under E1
  have maps2 := maps1.under E1
  have path2 := path1.under E1
  have ht2 := SyntaxCodedMixedTermTyping.target_type w.castSucc.castSucc (R 1).castSucc.castSucc (S 1).castSucc.castSucc (a 1).castSucc.castSucc (b 1).castSucc.castSucc (a 2).castSucc.castSucc (b 2).castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hE1
  let E2 := step w.castSucc.castSucc.castSucc (fun i => (a i).castSucc.castSucc.castSucc) (fun i => (b i).castSucc.castSucc.castSucc) (fun i => (R i).castSucc.castSucc.castSucc) (fun i => (S i).castSucc.castSucc.castSucc) 2 (Fin.last (m+1)).castSucc (Fin.last (m+2))
  let Γ3 := Context.add E2 (Context.image Formula.raise Γ2)
  apply Derives.exE (p := E2) (SyntaxCodedMixedTermExistence.exists_output h2.zf w.castSucc.castSucc (R 2).castSucc.castSucc (S 2).castSucc.castSucc (a 2).castSucc.castSucc (b 2).castSucc.castSucc (a 3).castSucc.castSucc (b 3).castSucc.castSucc (Fin.last (m+1)) h2.omega (.conjI (input_lists h2 2) ht2))
  have hE2 : Derives Γ3 E2 := .hyp (Or.inl rfl)
  have h3 := h2.under E2
  have maps3 := maps2.under E2
  have path3 := path2.under E2
  have ht3 : Derives _ (SyntaxTermSyntax.term w.castSucc.castSucc.castSucc (a 0).castSucc.castSucc.castSucc (b 0).castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxTermSyntax.term_rename]) (under (under (under ht E0) E1) E2)
  let E3 := step w.castSucc.castSucc.castSucc.castSucc (fun i => (a i).castSucc.castSucc.castSucc.castSucc) (fun i => (b i).castSucc.castSucc.castSucc.castSucc) (fun i => (R i).castSucc.castSucc.castSucc.castSucc) (fun i => (S i).castSucc.castSucc.castSucc.castSucc) 3 x.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3))
  let Γ4 := Context.add E3 (Context.image Formula.raise Γ3)
  apply Derives.exE (p := E3) (SyntaxCodedMixedTermExistence.exists_output h3.zf w.castSucc.castSucc.castSucc (R 3).castSucc.castSucc.castSucc (S 3).castSucc.castSucc.castSucc (a 0).castSucc.castSucc.castSucc (b 0).castSucc.castSucc.castSucc (a 3).castSucc.castSucc.castSucc (b 3).castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc h3.omega (.conjI (input_lists h3 3) ht3))
  have hE3 : Derives Γ4 E3 := .hyp (Or.inl rfl)
  have h4 := h3.under E3
  have maps4 := maps3.under E3
  have path4 := path3.under E3
  have p0 : Derives _ (step w.castSucc.castSucc.castSucc.castSucc (fun i => (a i).castSucc.castSucc.castSucc.castSucc) (fun i => (b i).castSucc.castSucc.castSucc.castSucc) (fun i => (R i).castSucc.castSucc.castSucc.castSucc) (fun i => (S i).castSucc.castSucc.castSucc.castSucc) 0 x.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, E0, step_rename]) (under (under (under hE0 E1) E2) E3)
  have p1 : Derives _ (step w.castSucc.castSucc.castSucc.castSucc (fun i => (a i).castSucc.castSucc.castSucc.castSucc) (fun i => (b i).castSucc.castSucc.castSucc.castSucc) (fun i => (R i).castSucc.castSucc.castSucc.castSucc) (fun i => (S i).castSucc.castSucc.castSucc.castSucc) 1 (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, E1, step_rename]) (under (under hE1 E2) E3)
  have p2 : Derives _ (step w.castSucc.castSucc.castSucc.castSucc (fun i => (a i).castSucc.castSucc.castSucc.castSucc) (fun i => (b i).castSucc.castSucc.castSucc.castSucc) (fun i => (R i).castSucc.castSucc.castSucc.castSucc) (fun i => (S i).castSucc.castSucc.castSucc.castSucc) 2 (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc) :=
    of_eq (by simp only [Formula.raise, E2, step_rename]) (under hE2 E3)
  have hr4 : Derives _ (SyntaxRenameTermSyntax.renamed w.castSucc.castSucc.castSucc.castSucc (U 0).castSucc.castSucc.castSucc.castSucc (V 0).castSucc.castSucc.castSucc.castSucc (a 0).castSucc.castSucc.castSucc.castSucc (b 0).castSucc.castSucc.castSucc.castSucc (A 0).castSucc.castSucc.castSucc.castSucc (b 0).castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc X.castSucc.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxRenameTermSyntax.renamed_rename]) (under (under (under (under hr E0) E1) E2) E3)
  exact at_old_path h4 maps4 path4 x.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) hr4 p0 p1 p2 hE3

private theorem fresh_step {m} {Γ : Context m} {w : Fin m} {a b A R S K H U V : Fin 4 → Fin m}
    (h : Basic Γ w a b A R S K H) (maps : Maps Γ w a b A U V) (e : Fin 4) (z x y : Fin m)
    (hz : Derives Γ (empty z)) (hx : Derives Γ (SyntaxVariableSyntax.code true w z x))
    (hs : Derives Γ (step w A b K H e x y)) : Derives Γ (SyntaxVariableSyntax.code true w z y) := by
  have hi := SyntaxCodedMixedBinderTyping.input_of_lifted _ _ _ _ _ _ _ _ _ _ _ (h.lifts e)
  have hc := Derives.conjL (.conjR (.conjL (.conjL hi)))
  let E := SyntaxMixedImageHead.head (old 2 w) (old 2 (A (dst e))) (old 2 (b (dst e))) (slot 2 0) (slot 2 1)
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ (SyntaxMixedImageHead.exists_head h.zf w (a (dst e)) (A (dst e)) (b (dst e)) h.omega (.conjL hc) (.conjR hc) (.conjR (.conjR hi)))
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 h.zf E
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 h.omega E)
  have hz2 := of_eq (empty_rename z (old 2)) (HornBinderRules.under_body 2 hz E)
  have hez := OmegaUniversal.empty_unique (slot 2 0) (old 2 z) (ZFContext.arithmetic hZ2).base.extensionality (.conjL hE) hz2
  have hn := AbstractVariableIndex.code_index_subst true (old 2 w) (slot 2 0) (old 2 z) (slot 2 1) hez (.conjL (.conjR hE))
  have hh : Derives Δ (SyntaxMixedImageHead.head (old 2 w) (old 2 (A (dst e))) (old 2 (b (dst e))) (old 2 z) (slot 2 1)) :=
    .conjI hz2 (.conjI hn (.conjR (.conjR hE)))
  have hl2 := of_eq (liftAt_rename w a b A R S K H e (old 2)) (HornBinderRules.under_body 2 (h.lifts e) E)
  have hu2 := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w (a (dst e)) (A (dst e)) (U (dst e)) (old 2)) (HornBinderRules.under_body 2 (maps.shifts (dst e)) E)
  have hv2 := of_eq (SyntaxIdentityMapSyntax.identityMap_rename w (b (dst e)) (V (dst e)) (old 2)) (HornBinderRules.under_body 2 (maps.identities (dst e)) E)
  have hf := SyntaxCodedMixedTermFields.at_field hZ2 true (old 2 w) (old 2 (K e)) (old 2 (H e)) (old 2 (A (src e))) (old 2 (b (src e)))
    (old 2 (A (dst e))) (old 2 (b (dst e))) (old 2 x) (old 2 y) (old 2 z) hw2
    (of_eq (SyntaxMixedImageCodeSyntax.termLists_rename w (A (src e)) (b (src e)) (A (dst e)) (b (dst e)) (K e) (H e) (old 2)) (HornBinderRules.under_body 2 (output_lists h e) E))
    (of_eq (SyntaxVariableSyntax.code_rename true w z x (old 2)) (HornBinderRules.under_body 2 hx E))
  have hfield := Derives.impE (.conjL hf) (of_eq (step_rename w A b K H e x y (old 2)) (HornBinderRules.under_body 2 hs E))
  have hzfield := SyntaxCodedMixedBinderFields.zero_iff hZ2 (old 2 w) (old 2 (R e)) (old 2 (S e))
    (old 2 (a (src e))) (old 2 (b (src e))) (old 2 (a (dst e))) (old 2 (b (dst e))) (old 2 (A (src e))) (old 2 (A (dst e)))
    (old 2 (K e)) (old 2 (H e)) (old 2 (U (dst e))) (old 2 (V (dst e))) (old 2 z) (slot 2 1) (old 2 y) hw2 hl2 hu2 hv2 hh
  have hy := Derives.impE (.conjL hzfield) hfield
  exact of_eq (SyntaxVariableSyntax.code_rename true w z y (old 2)).symm
    (.impE (.conjR (AbstractBinderRename.code_iff_equal hZ2 true (old 2 w) (old 2 z) (slot 2 1) (old 2 y) hw2 hn)) hy)

private theorem fresh_path {m} {Γ : Context m} {w X I J Y O : Fin m} {a b A R S K H U V : Fin 4 → Fin m}
    (h : Basic Γ w a b A R S K H) (maps : Maps Γ w a b A U V) (path : Path Γ w A b K H X I J Y O)
    (z : Fin m) (hz : Derives Γ (empty z)) (hx : Derives Γ (SyntaxVariableSyntax.code true w z X)) : Derives Γ (.equal Y O) := by
  have h1 := fresh_step h maps 0 z X I hz hx path.first
  have h2 := fresh_step h maps 1 z I J hz h1 path.second
  have h3 := fresh_step h maps 2 z J Y hz h2 path.third
  have h4 := fresh_step h maps 3 z X O hz hx path.direct
  exact SyntaxVariables.unique h.zf true w z Y O h.omega h3 h4

private theorem at_old_variable {m} {Γ : Context m} {w X I J Y O : Fin m} {a b A R S K H U V : Fin 4 → Fin m}
    (h : Basic Γ w a b A R S K H) (maps : Maps Γ w a b A U V) (path : Path Γ w A b K H X I J Y O)
    (bound : Bool) (i k : Fin m) (hx : Derives Γ (SyntaxVariableSyntax.code bound w (if bound then k else i) X))
    (hi : Derives Γ (.mem i (SyntaxTermSyntax.limit bound (a 0) (b 0))))
    (hk : Derives Γ (ForcingOpenLift.step bound i k)) : Derives Γ (.equal Y O) := by
  have hn := node_spec h 0
  have hlim : Derives Γ (.mem (SyntaxTermSyntax.limit bound (a 0) (b 0)) w) := by
    cases bound
    · exact .conjL (.conjR hn)
    · exact .conjL hn
  have hin := StructuralListTraceOrder.member_member h.zf w i (SyntaxTermSyntax.limit bound (a 0) (b 0)) h.omega hlim hi
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxVariableSyntax.code bound w.castSucc i.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (SyntaxVariables.exists_code h.zf bound w i h.omega hin)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h1 := h.under E
  have maps1 := maps.under E
  have path1 := path.under E
  have hn1 := node_spec h1 0
  have hi1 : Derives Δ (.mem i.castSucc (SyntaxTermSyntax.limit bound (a 0).castSucc (b 0).castSucc)) :=
    of_eq (by simp only [Formula.raise, Formula.rename, SyntaxTermSyntax.limit_map]) (under hi E)
  have hType := SyntaxTermSyntax.intro_term bound w.castSucc (a 0).castSucc (b 0).castSucc (Fin.last m) i.castSucc
    (.conjI (.conjI (.conjL hn1) (.conjL (.conjR hn1))) hi1) (.conjR hE)
  have hx1 : Derives Δ (SyntaxVariableSyntax.code bound w.castSucc (if bound then k.castSucc else i.castSucc) X.castSucc) :=
    of_eq (by cases bound <;> simp only [Formula.raise, SyntaxVariableSyntax.code_rename, Bool.false_eq_true, ↓reduceIte]) (under hx E)
  have hk1 := of_eq (ForcingOpenLift.step_rename bound i k Fin.castSucc) (under hk E)
  have hr : Derives Δ (SyntaxRenameTermSyntax.renamed w.castSucc (U 0).castSucc (V 0).castSucc (a 0).castSucc (b 0).castSucc (A 0).castSucc (b 0).castSucc (Fin.last m) X.castSucc) := by
    cases bound with
    | true => exact .impE (.conjR (AbstractBinderRename.bound_at h1.zf _ _ _ _ _ _ _ _ i.castSucc k.castSucc h1.omega (maps1.shifts 0) (maps1.identities 0) hType (.conjR hE) hk1)) hx1
    | false => exact .impE (.conjR (AbstractBinderRename.free_at h1.zf _ _ _ _ _ _ _ _ i.castSucc h1.omega (maps1.shifts 0) (maps1.identities 0) hType (.conjR hE))) hx1
  exact from_old_source h1 maps1 path1 (Fin.last m) hr

private theorem at_candidate {m} {Γ : Context m} {w X I J Y O : Fin m} {a b A R S K H U V : Fin 4 → Fin m}
    (h : Basic Γ w a b A R S K H) (maps : Maps Γ w a b A U V) (path : Path Γ w A b K H X I J Y O) :
    Derives Γ (.equal Y O) := by
  have ht := SyntaxCodedMixedTermTyping.source_type w (K 0) (H 0) (A 0) (b 0) (A 1) (b 1) X I path.first
  apply Derives.disjE (.conjR ht)
  · let E := SyntaxTermSyntax.branch true w (A 0) X
    let B := SyntaxTermSyntax.branchWitness true w (A 0) X
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply SyntaxTermSyntax.eliminate_branch true w (A 0) X _ (.hyp (Or.inl rfl))
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have h1 := (h.add E).under B
    have maps1 := (maps.add E).under B
    have path1 := (path.add E).under B
    have hn := SyntaxVariableDecode.index_natural true w.castSucc (Fin.last m) X.castSucc (.conjR hB)
    have split := OmegaStructureInduction.decomposition w.castSucc (ZFContext.separation h1.zf OmegaStructureSyntax.splitMatrix) h1.omega
    apply Derives.disjE (OmegaStructureAlgebra.decomposition_at w.castSucc (Fin.last m) split hn)
    · exact fresh_path (h1.add _) (maps1.add _) (path1.add _) (Fin.last m) (.hyp (Or.inl rfl)) (add (.conjR hB) _)
    · let E' := OmegaStructureSyntax.predecessor w.castSucc (Fin.last m)
      let F := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (successor (Fin.last m).castSucc (Fin.last (m+1)))
      let Ξ := Context.add F (Context.image Formula.raise (Context.add E' Δ))
      apply Derives.exE (p := F) (.hyp (Or.inl rfl))
      have hF : Derives Ξ F := .hyp (Or.inl rfl)
      have h2 := (h1.add E').under F
      have maps2 := (maps1.add E').under F
      have path2 := (path1.add E').under F
      have hnode := node_spec h2 0
      have hmem : Derives Ξ (.mem (Fin.last m).castSucc (A 0).castSucc.castSucc) := under (add (.conjL hB) E') F
      have hi := SyntaxIndexLiftOrder.predecessor_member h2.zf w.castSucc.castSucc (a 0).castSucc.castSucc (A 0).castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) h2.omega (.conjL hnode) (.conjR (.conjR hnode)) hmem (.conjR hF)
      have hc := of_eq (SyntaxVariableSyntax.code_rename true w.castSucc (Fin.last m) X.castSucc Fin.castSucc) (under (add (.conjR hB) E') F)
      exact at_old_variable h2 maps2 path2 true (Fin.last (m+1)) (Fin.last m).castSucc hc hi (.conjR hF)
  · let E := SyntaxTermSyntax.branch false w (b 0) X
    let B := SyntaxTermSyntax.branchWitness false w (b 0) X
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply SyntaxTermSyntax.eliminate_branch false w (b 0) X _ (.hyp (Or.inl rfl))
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hs : Derives Δ (ForcingOpenLift.step false (Fin.last m) (Fin.last m)) := .impI (.hyp (Or.inl rfl))
    exact at_old_variable ((h.add E).under B) ((maps.add E).under B) ((path.add E).under B) false (Fin.last m) (Fin.last m) (.conjR hB) (.conjL hB) hs

private theorem Basic.in_body {m} {Γ : Context m} {w : Fin m} {a b A R S K H : Fin 4 → Fin m}
    (h : Basic Γ w a b A R S K H) (k : Nat) (D : Formula (m+k)) :
    Basic (Context.add D (raisedContext k Γ)) (old k w) (fun i => old k (a i)) (fun i => old k (b i)) (fun i => old k (A i)) (fun i => old k (R i)) (fun i => old k (S i)) (fun i => old k (K i)) (fun i => old k (H i)) := {
  zf := HornBinderRules.zf_body k h.zf D
  omega := of_eq (omega_rename w (old k)) (HornBinderRules.under_body k h.omega D)
  oldDiagram := of_eq (diagram_rename w a b R S (old k)) (HornBinderRules.under_body k h.oldDiagram D)
  lifts := fun e => of_eq (liftAt_rename w a b A R S K H e (old k)) (HornBinderRules.under_body k (h.lifts e) D)
}

private theorem Maps.in_body {m} {Γ : Context m} {w : Fin m} {a b A U V : Fin 4 → Fin m}
    (h : Maps Γ w a b A U V) (k : Nat) (D : Formula (m+k)) :
    Maps (Context.add D (raisedContext k Γ)) (old k w) (fun i => old k (a i)) (fun i => old k (b i)) (fun i => old k (A i)) (fun i => old k (U i)) (fun i => old k (V i)) := {
  shifts := fun i => of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w (a i) (A i) (U i) (old k)) (HornBinderRules.under_body k (h.shifts i) D)
  identities := fun i => of_eq (SyntaxIdentityMapSyntax.identityMap_rename w (b i) (V i) (old k)) (HornBinderRules.under_body k (h.identities i) D)
}

private theorem closure_at_maps {m} {Γ : Context m} {w : Fin m} {a b A R S K H U V : Fin 4 → Fin m}
    (h : Basic Γ w a b A R S K H) (maps : Maps Γ w a b A U V) : Derives Γ (diagram w A b K H) := by
  apply OriginalUniversalBlock.intro_many 5
  apply Derives.impI
  let D := runs (old 5 w) (fun i => old 5 (A i)) (fun i => old 5 (b i)) (fun i => old 5 (K i)) (fun i => old 5 (H i))
    (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) (slot 5 4)
  let Δ := Context.add D (raisedContext 5 Γ)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have p : Path Δ (old 5 w) (fun i => old 5 (A i)) (fun i => old 5 (b i)) (fun i => old 5 (K i)) (fun i => old 5 (H i))
      (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) (slot 5 4) := {
    first := .conjL hD
    second := .conjL (.conjR hD)
    third := .conjL (.conjR (.conjR hD))
    direct := .conjR (.conjR (.conjR hD))
  }
  exact at_candidate (h.in_body 5 D) (maps.in_body 5 D) p

/-- Four ACTUAL original mixed binder advances; no new transition relation. -/
def lifts {m} (w : Fin m) (a b A R S K H : Fin 4 → Fin m) : Formula m :=
  (liftAt w a b A R S K H 0).conj ((liftAt w a b A R S K H 1).conj
    ((liftAt w a b A R S K H 2).conj (liftAt w a b A R S K H 3)))

theorem lifts_rename {m l} (w : Fin m) (a b A R S K H : Fin 4 → Fin m) (r : Fin m → Fin l) :
    (lifts w a b A R S K H).rename r = lifts (r w) (fun i => r (a i)) (fun i => r (b i)) (fun i => r (A i))
      (fun i => r (R i)) (fun i => r (S i)) (fun i => r (K i)) (fun i => r (H i)) := by
  simp only [lifts, Formula.rename, liftAt_rename]

/-- The WHOLE actual four-table term diagram is preserved by original
mixed binder advances. All eight structural maps and all old path outputs
are constructed and eliminated inside the object theory, including at
nonstandard scopes. No map, old-run or variable-case premise is retained. -/
theorem lifted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (a b A R S K H : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (diagram w a b R S)) (hl : Derives Γ (lifts w a b A R S K H)) :
    Derives Γ (diagram w A b K H) := by
  let h0 : Basic Γ w a b A R S K H := {
    zf := hZ
    omega := hw
    oldDiagram := hd
    lifts := Fin.cases (.conjL hl) (Fin.cases (.conjL (.conjR hl))
      (Fin.cases (.conjL (.conjR (.conjR hl))) (Fin.cases (.conjR (.conjR (.conjR hl))) (fun z => Fin.elim0 z))))
  }
  have node0 := node_spec h0 0
  let E0 := SyntaxFreeShiftSyntax.shiftMap w.castSucc (a 0).castSucc (A 0).castSucc (Fin.last m)
  let Γ1 := Context.add E0 (Context.image Formula.raise Γ)
  apply Derives.exE (p := E0) (SyntaxFreeShiftGraph.exists_map h0.zf w (a 0) (A 0) h0.omega (.conjL node0) (.conjR (.conjR node0)))
  have hE0 : Derives Γ1 E0 := .hyp (Or.inl rfl)
  have h1 := h0.under E0
  have node1 := node_spec h1 0
  let E1 := SyntaxIdentityMapSyntax.identityMap w.castSucc.castSucc (b 0).castSucc.castSucc (Fin.last (m+1))
  let Γ2 := Context.add E1 (Context.image Formula.raise Γ1)
  apply Derives.exE (p := E1) (SyntaxIdentityGraph.exists_map h1.zf w.castSucc (b 0).castSucc (.conjL (.conjR node1)))
  have hE1 : Derives Γ2 E1 := .hyp (Or.inl rfl)
  have h2 := h1.under E1
  have node2 := node_spec h2 1
  let E2 := SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc.castSucc (a 1).castSucc.castSucc.castSucc (A 1).castSucc.castSucc.castSucc (Fin.last (m+2))
  let Γ3 := Context.add E2 (Context.image Formula.raise Γ2)
  apply Derives.exE (p := E2) (SyntaxFreeShiftGraph.exists_map h2.zf w.castSucc.castSucc (a 1).castSucc.castSucc (A 1).castSucc.castSucc h2.omega (.conjL node2) (.conjR (.conjR node2)))
  have hE2 : Derives Γ3 E2 := .hyp (Or.inl rfl)
  have h3 := h2.under E2
  have node3 := node_spec h3 1
  let E3 := SyntaxIdentityMapSyntax.identityMap w.castSucc.castSucc.castSucc.castSucc (b 1).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3))
  let Γ4 := Context.add E3 (Context.image Formula.raise Γ3)
  apply Derives.exE (p := E3) (SyntaxIdentityGraph.exists_map h3.zf w.castSucc.castSucc.castSucc (b 1).castSucc.castSucc.castSucc (.conjL (.conjR node3)))
  have hE3 : Derives Γ4 E3 := .hyp (Or.inl rfl)
  have h4 := h3.under E3
  have node4 := node_spec h4 2
  let E4 := SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc.castSucc.castSucc.castSucc (a 2).castSucc.castSucc.castSucc.castSucc.castSucc (A 2).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4))
  let Γ5 := Context.add E4 (Context.image Formula.raise Γ4)
  apply Derives.exE (p := E4) (SyntaxFreeShiftGraph.exists_map h4.zf w.castSucc.castSucc.castSucc.castSucc (a 2).castSucc.castSucc.castSucc.castSucc (A 2).castSucc.castSucc.castSucc.castSucc h4.omega (.conjL node4) (.conjR (.conjR node4)))
  have hE4 : Derives Γ5 E4 := .hyp (Or.inl rfl)
  have h5 := h4.under E4
  have node5 := node_spec h5 2
  let E5 := SyntaxIdentityMapSyntax.identityMap w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (b 2).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+5))
  let Γ6 := Context.add E5 (Context.image Formula.raise Γ5)
  apply Derives.exE (p := E5) (SyntaxIdentityGraph.exists_map h5.zf w.castSucc.castSucc.castSucc.castSucc.castSucc (b 2).castSucc.castSucc.castSucc.castSucc.castSucc (.conjL (.conjR node5)))
  have hE5 : Derives Γ6 E5 := .hyp (Or.inl rfl)
  have h6 := h5.under E5
  have node6 := node_spec h6 3
  let E6 := SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (a 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (A 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+6))
  let Γ7 := Context.add E6 (Context.image Formula.raise Γ6)
  apply Derives.exE (p := E6) (SyntaxFreeShiftGraph.exists_map h6.zf w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (a 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (A 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc h6.omega (.conjL node6) (.conjR (.conjR node6)))
  have hE6 : Derives Γ7 E6 := .hyp (Or.inl rfl)
  have h7 := h6.under E6
  have node7 := node_spec h7 3
  let E7 := SyntaxIdentityMapSyntax.identityMap w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (b 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+7))
  let Γ8 := Context.add E7 (Context.image Formula.raise Γ7)
  apply Derives.exE (p := E7) (SyntaxIdentityGraph.exists_map h7.zf w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (b 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (.conjL (.conjR node7)))
  have hE7 : Derives Γ8 E7 := .hyp (Or.inl rfl)
  have h8 := h7.under E7
  have p0 : Derives Γ8 (SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (a 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (A 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq
    (by simp only [Formula.raise, E0, SyntaxFreeShiftSyntax.shiftMap_rename]) (under (under (under (under (under (under (under hE0 E1) E2) E3) E4) E5) E6) E7)
  have p1 : Derives Γ8 (SyntaxIdentityMapSyntax.identityMap w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (b 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq
    (by simp only [Formula.raise, E1, SyntaxIdentityMapSyntax.identityMap_rename]) (under (under (under (under (under (under hE1 E2) E3) E4) E5) E6) E7)
  have p2 : Derives Γ8 (SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (a 1).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (A 1).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq
    (by simp only [Formula.raise, E2, SyntaxFreeShiftSyntax.shiftMap_rename]) (under (under (under (under (under hE2 E3) E4) E5) E6) E7)
  have p3 : Derives Γ8 (SyntaxIdentityMapSyntax.identityMap w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (b 1).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc.castSucc) := of_eq
    (by simp only [Formula.raise, E3, SyntaxIdentityMapSyntax.identityMap_rename]) (under (under (under (under hE3 E4) E5) E6) E7)
  have p4 : Derives Γ8 (SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (a 2).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (A 2).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc.castSucc) := of_eq
    (by simp only [Formula.raise, E4, SyntaxFreeShiftSyntax.shiftMap_rename]) (under (under (under hE4 E5) E6) E7)
  have p5 : Derives Γ8 (SyntaxIdentityMapSyntax.identityMap w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (b 2).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+5)).castSucc.castSucc) := of_eq
    (by simp only [Formula.raise, E5, SyntaxIdentityMapSyntax.identityMap_rename]) (under (under hE5 E6) E7)
  have p6 : Derives Γ8 (SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (a 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (A 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+6)).castSucc) := of_eq
    (by simp only [Formula.raise, E6, SyntaxFreeShiftSyntax.shiftMap_rename]) (under hE6 E7)
  have p7 : Derives Γ8 (SyntaxIdentityMapSyntax.identityMap w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (b 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+7))) := hE7
  let U : Fin 4 → Fin (m+8) := Fin.cases (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.cases (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.cases (Fin.last (m+4)).castSucc.castSucc.castSucc (fun _ => (Fin.last (m+6)).castSucc)))
  let V : Fin 4 → Fin (m+8) := Fin.cases (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.cases (Fin.last (m+3)).castSucc.castSucc.castSucc.castSucc (Fin.cases (Fin.last (m+5)).castSucc.castSucc (fun _ => (Fin.last (m+7)))))
  have maps : Maps Γ8 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (fun i => (a i).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) (fun i => (b i).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) (fun i => (A i).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) U V := {
    shifts := Fin.cases p0 (Fin.cases p2 (Fin.cases p4 (Fin.cases p6 (fun z => Fin.elim0 z))))
    identities := Fin.cases p1 (Fin.cases p3 (Fin.cases p5 (Fin.cases p7 (fun z => Fin.elim0 z))))
  }
  exact of_eq (by simp only [Formula.raise, diagram_rename]) (closure_at_maps h8 maps)

def input {m} (w : Fin m) (a b A R S K H : Fin 4 → Fin m) : Formula m :=
  (omega w).conj ((diagram w a b R S).conj (lifts w a b A R S K H))

def sentence {m} (w : Fin m) (a b A R S K H : Fin 4 → Fin m) : Source.Sentence :=
  ((input w a b A R S K H).imp (diagram w A b K H)).close

theorem kernel_certificate {m} (w : Fin m) (a b A R S K H : Fin 4 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence w a b A R S K H)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input w a b A R S K H
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact lifted (ZFContext.add (ZFContext.source_ZF m) E) w a b A R S K H (.conjL h) (.conjL (.conjR h)) (.conjR (.conjR h))

private def quad {m} (a b c d : Fin m) : Fin 4 → Fin m :=
  Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))

/-- The ACTUAL root tables: original rebind, lifted pointwise opening,
original InstantiateTop coded environment, and direct pointwise opening. -/
def rootDiagram {m} (w z a f T A C R S K H r s : Fin m) (d : Fin 6 → Fin m) : Formula m :=
  diagram w (quad a A C z) (quad f f T T) (quad (d 3) K r R) (quad (d 5) H s S)

/-- Package the already proved root term triangle as the actual coded
four-table invariant. The original mode2/coded bridge is REUSED; no Run
judgment or equality answer is supplied. Every term candidate is object
quantified in rootDiagram. -/
theorem root {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode z a f T A C R S K H j n q P r s : Fin m) (d : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode)) (hz : Derives Γ (empty z))
    (he : Derives Γ (ForcingOpenLayout.environment w z a f T R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H))
    (hd : Derives Γ (ForcingConditionRebind.data w a f A j n q d)) (hj : Derives Γ (.mem j f))
    (hp : Derives Γ (StructuralListFieldSyntax.field w S j P))
    (hi : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z T C P r s)) :
    Derives Γ (rootDiagram w z a f T A C R S K H r s d) := by
  have hf := InstantiateOperationFrameRoot.from_actual_input hZ w mode z P T C r s hw hm hz hi
  apply OriginalUniversalBlock.intro_many 5
  apply Derives.impI
  let D := runs (old 5 w) (fun i => old 5 (quad a A C z i)) (fun i => old 5 (quad f f T T i))
    (fun i => old 5 (quad (d 3) K r R i)) (fun i => old 5 (quad (d 5) H s S i))
    (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) (slot 5 4)
  let Δ := Context.add D (raisedContext 5 Γ)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have hZ5 := HornBinderRules.zf_body 5 hZ D
  have hw5 := of_eq (omega_rename w (old 5)) (HornBinderRules.under_body 5 hw D)
  have hf5 := of_eq (InstantiateOperationFrameSyntax.frame_rename w mode z P C T z T r s (old 5)) (HornBinderRules.under_body 5 hf D)
  have hr := Derives.conjR (Derives.impE (.conjR (InstantiateFrameTerm.guarded_coded_iff hZ5
    (old 5 w) (old 5 mode) (old 5 z) (old 5 P) (old 5 C) (old 5 T) (old 5 z) (old 5 T) (old 5 r) (old 5 s)
    (slot 5 2) (slot 5 3) hw5 hf5)) (.conjL (.conjR (.conjR hD))))
  exact ForcingRebindOpeningTriangle.term hZ5 (old 5 w) (old 5 mode) (old 5 z) (old 5 a) (old 5 f) (old 5 T) (old 5 A) (old 5 C)
    (old 5 R) (old 5 S) (old 5 K) (old 5 H) (old 5 j) (old 5 n) (old 5 q) (old 5 P)
    (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) (slot 5 4) (fun i => old 5 (d i))
    hw5 (of_eq (SyntaxNumeralSyntax.numeral_rename 2 mode (old 5)) (HornBinderRules.under_body 5 hm D))
    (of_eq (empty_rename z (old 5)) (HornBinderRules.under_body 5 hz D))
    (of_eq (ForcingOpenLayout.environment_rename w z a f T R S (old 5)) (HornBinderRules.under_body 5 he D))
    (of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w R S a f z T A C K H (old 5)) (HornBinderRules.under_body 5 hl D))
    (of_eq (ForcingConditionRebind.data_rename w a f A j n q d (old 5)) (HornBinderRules.under_body 5 hd D))
    (HornBinderRules.under_body 5 hj D)
    (of_eq (StructuralListFieldSyntax.field_rename w S j P (old 5)) (HornBinderRules.under_body 5 hp D))
    (.conjL hD) (.conjL (.conjR hD)) hr (.conjR (.conjR (.conjR hD)))

def rootInput {m} (w mode z a f T A C R S K H j n q P r s : Fin m) (d : Fin 6 → Fin m) : Formula m :=
  (omega w).conj ((SyntaxNumeralSyntax.numeral 2 mode).conj ((empty z).conj
    ((ForcingOpenLayout.environment w z a f T R S).conj ((SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H).conj
      ((ForcingConditionRebind.data w a f A j n q d).conj ((Formula.mem j f).conj
        ((StructuralListFieldSyntax.field w S j P).conj (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z T C P r s))))))))

def rootSentence {m} (w mode z a f T A C R S K H j n q P r s : Fin m) (d : Fin 6 → Fin m) : Source.Sentence :=
  ((rootInput w mode z a f T A C R S K H j n q P r s d).imp (rootDiagram w z a f T A C R S K H r s d)).close

theorem root_kernel_certificate {m} (w mode z a f T A C R S K H j n q P r s : Fin m) (d : Fin 6 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (rootSentence w mode z a f T A C R S K H j n q P r s d)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := rootInput w mode z a f T A C R S K H j n q P r s d
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact root (ZFContext.add (ZFContext.source_ZF m) E) w mode z a f T A C R S K H j n q P r s d
    (.conjL h) (.conjL (.conjR h)) (.conjL (.conjR (.conjR h)))
    (.conjL (.conjR (.conjR (.conjR h)))) (.conjL (.conjR (.conjR (.conjR (.conjR h)))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR h)))))) (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h)))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h))))))))
    (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h))))))))

end PPAC.Migration.ForcingTermDiagram
