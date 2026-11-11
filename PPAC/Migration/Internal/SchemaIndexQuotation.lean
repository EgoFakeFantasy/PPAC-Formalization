import PPAC.Migration.Internal.SchemaIndexRenameSystem
import PPAC.Migration.Internal.IndexTermImageCodeFields
import YesMetaZFC.SetTheory.Binding

/-! Exact numeric values of the THREE ORIGINAL schema embedding graphs.
Only original successor maps and binder lifts are consumed. All code values
are object variables; the quoted parameter count is an external scheme index. -/
namespace PPAC.Migration.Internal.SchemaIndexQuotation
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

/-- At quoted finite positions the ACTUAL graph has its original native value. -/
def value {m} (i j : Nat) (g : Fin m) : Source.Formula m := .all (.all
  (((SyntaxNumeralSyntax.numeral i (Fin.last m).castSucc).conj
    (SyntaxNumeralSyntax.numeral j (Fin.last (m+1)))).imp
      (edge g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))))

theorem value_rename {m l} (i j : Nat) (g : Fin m) (r : Fin m → Fin l) :
    (value i j g).rename r = value i j (r g) := by
  simp only [value,Formula.rename,SyntaxNumeralSyntax.numeral_rename,edge_rename,
    Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem value_at {m} {Γ : Context m} (i j : Nat) (g x y : Fin m)
    (h : Derives Γ (value i j g)) (hx : Derives Γ (SyntaxNumeralSyntax.numeral i x))
    (hy : Derives Γ (SyntaxNumeralSyntax.numeral j y)) : Derives Γ (edge g x y) :=
  .impE (of_eq (by simp only [Formula.instantiate,Formula.rename,
    SyntaxNumeralSyntax.numeral_rename,edge_rename,Formula.liftRen,
    Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE y (Derives.allE x h))) (.conjI hx hy)

private theorem member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {n : Nat} (j : Fin n) (a x : Fin m)
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral n a)) (hx : Derives Γ (SyntaxNumeralSyntax.numeral j.val x)) :
    Derives Γ (.mem x a) :=
  .impE (.conjR (SyntaxNumeralMembers.member_iff hZ n a x ha)) (SyntaxPositionSyntax.intro_below n j x hx)

private theorem successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (x y : Fin m)
    (hx : Derives Γ (SyntaxNumeralSyntax.numeral k x)) (hy : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) y)) :
    Derives Γ (OmegaSyntax.successor y x) := by
  let B := (SyntaxNumeralSyntax.numeral k (Fin.last m)).conj (OmegaSyntax.successor y.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply SyntaxNumeralSyntax.eliminate_succ k y _ hy
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hx1 := of_eq (SyntaxNumeralSyntax.numeral_rename k x Fin.castSucc) (under hx B)
  have he := SyntaxNumerals.unique (ZFContext.under hZ B) k (Fin.last m) x.castSucc (.conjL hB) hx1
  exact of_eq (successor_rename y x Fin.castSucc).symm
    (GodelUnpairArithmetic.successor_base_subst _ _ _ he (.conjR hB))

theorem shift_value {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c r : Fin m)
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral n a)) (hr : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w a c r))
    (j : Fin n) : Derives Γ (value j.val (j.val+1) r) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let B := (SyntaxNumeralSyntax.numeral j.val (Fin.last m).castSucc).conj
    (SyntaxNumeralSyntax.numeral (j.val+1) (Fin.last (m+1)))
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have ha2 : Derives Δ (SyntaxNumeralSyntax.numeral n a.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 ha B)
  have hr2 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc r.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,SyntaxFreeShiftSyntax.shiftMap_rename]) (SyntaxRenameBinders.under_2 hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact .impE (.conjR (SyntaxFreeShiftGraph.edge_iff _ _ _ _ (SyntaxFreeShiftGraph.to_graph _ _ _ _ hr2)))
    (.conjI (member hZ2 j _ _ ha2 (.conjL hB)) (successor hZ2 j.val _ _ (.conjL hB) (.conjR hB)))

private theorem double_value {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b c r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (SyntaxNumeralSyntax.numeral n a)) (hr : Derives Γ (SchemaDoubleShiftSyntax.map w a b c r))
    (j : Fin n) : Derives Γ (value j.val (j.val+2) r) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let B := (SyntaxNumeralSyntax.numeral j.val (Fin.last m).castSucc).conj
    (SyntaxNumeralSyntax.numeral (j.val+2) (Fin.last (m+1)))
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have ha2 : Derives Δ (SyntaxNumeralSyntax.numeral n a.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 ha B)
  have hr2 : Derives Δ (SchemaDoubleShiftSyntax.map w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc r.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,SchemaDoubleShiftSyntax.map_rename]) (SyntaxRenameBinders.under_2 hr B)
  have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  let P := (Source.Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj
    (SyntaxNumeralSyntax.numeral (j.val+1) (Fin.last (m+2)))
  let Ξ := Context.add P (Context.image Formula.raise Δ)
  apply Derives.exE (p := P) (SyntaxNumerals.exists_numeral hZ2 (j.val+1) w.castSucc.castSucc hw2)
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  have hZ3 := ZFContext.under hZ2 P
  have hx : Derives Ξ (SyntaxNumeralSyntax.numeral j.val (Fin.last m).castSucc.castSucc) :=
    of_eq (SyntaxNumeralSyntax.numeral_rename _ _ Fin.castSucc) (under (.conjL hB) P)
  have hy : Derives Ξ (SyntaxNumeralSyntax.numeral (j.val+2) (Fin.last (m+1)).castSucc) :=
    of_eq (SyntaxNumeralSyntax.numeral_rename _ _ Fin.castSucc) (under (.conjR hB) P)
  have hd := SchemaDoubleShiftSyntax.intro_displacement _ _ (Fin.last (m+2))
    (successor hZ3 j.val _ _ hx (.conjR hP)) (successor hZ3 (j.val+1) _ _ (.conjR hP) hy)
  have hr3 := of_eq (SchemaDoubleShiftSyntax.map_rename _ _ _ _ _ Fin.castSucc) (under hr2 P)
  have hmem := under (member hZ2 j _ _ ha2 (.conjL hB)) P
  have ho := Derives.impE (.conjR (SchemaDoubleShiftGraph.edge_iff hZ3 _ _ _ _ _ _ _ hr3)) (.conjI hmem hd)
  exact of_eq (edge_rename _ _ _ Fin.castSucc).symm ho

private theorem lift_value {m n p} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (f : Fin n → Fin p) (w a c u v r g : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral n a))
    (hh : Derives Γ (SyntaxIndexLiftSyntax.lifted w r a c u v g))
    (hp : ∀ j : Fin n, Derives Γ (value j.val (f j).val r)) (j : Fin (n+1)) :
    Derives Γ (value j.val (YesMetaZFC.SetTheory.BoundEmbedding.lift f j).val g) := by
  refine Fin.cases ?_ (fun j => ?_) j
  · change Derives Γ (value 0 0 g)
    apply Derives.allI
    apply Derives.allI
    apply Derives.impI
    let B := (SyntaxNumeralSyntax.numeral 0 (Fin.last m).castSucc).conj
      (SyntaxNumeralSyntax.numeral 0 (Fin.last (m+1)))
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
    have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
    have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise,omega_rename]) (SyntaxRenameBinders.under_2 hw B)
    have hh2 : Derives Δ (SyntaxIndexLiftSyntax.lifted w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc u.castSucc.castSucc v.castSucc.castSucc g.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise,SyntaxIndexLiftSyntax.lifted_rename]) (SyntaxRenameBinders.under_2 hh B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    exact .impE (.conjR (SyntaxIndexLiftEdges.zero_iff hZ2 _ _ _ _ _ _ _ _ _ hw2 hh2 (.conjL hB))) (.conjR hB)
  · change Derives Γ (value (j.val+1) ((f j).val+1) g)
    apply Derives.allI
    apply Derives.allI
    apply Derives.impI
    let B := (SyntaxNumeralSyntax.numeral (j.val+1) (Fin.last m).castSucc).conj
      (SyntaxNumeralSyntax.numeral ((f j).val+1) (Fin.last (m+1)))
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
    have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise,omega_rename]) (SyntaxRenameBinders.under_2 hw B)
    have ha2 : Derives Δ (SyntaxNumeralSyntax.numeral n a.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise,SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 ha B)
    have hh2 : Derives Δ (SyntaxIndexLiftSyntax.lifted w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc u.castSucc.castSucc v.castSucc.castSucc g.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise,SyntaxIndexLiftSyntax.lifted_rename]) (SyntaxRenameBinders.under_2 hh B)
    have hp2 : Derives Δ (value j.val (f j).val r.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise,value_rename]) (SyntaxRenameBinders.under_2 (hp j) B)
    let X := (SyntaxNumeralSyntax.numeral j.val (Fin.last (m+2))).conj
      (OmegaSyntax.successor (Fin.last m).castSucc.castSucc (Fin.last (m+2)))
    let Ξ := Context.add X (Context.image Formula.raise Δ)
    apply SyntaxNumeralSyntax.eliminate_succ j.val (Fin.last m).castSucc _ (.conjL hB)
    have hX : Derives Ξ X := .hyp (Or.inl rfl)
    have hy3 : Derives Ξ (SyntaxNumeralSyntax.numeral ((f j).val+1) (Fin.last (m+1)).castSucc) :=
      of_eq (SyntaxNumeralSyntax.numeral_rename _ _ Fin.castSucc) (under (.conjR hB) X)
    let Y := (SyntaxNumeralSyntax.numeral (f j).val (Fin.last (m+3))).conj
      (OmegaSyntax.successor (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+3)))
    let Ω := Context.add Y (Context.image Formula.raise Ξ)
    apply SyntaxNumeralSyntax.eliminate_succ (f j).val (Fin.last (m+1)).castSucc _ hy3
    have hY : Derives Ω Y := .hyp (Or.inl rfl)
    have hZ4 := ZFContext.under (ZFContext.under hZ2 X) Y
    have hw4 : Derives Ω (omega w.castSucc.castSucc.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise,omega_rename]) (under (under hw2 X) Y)
    have ha4 : Derives Ω (SyntaxNumeralSyntax.numeral n a.castSucc.castSucc.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise,SyntaxNumeralSyntax.numeral_rename]) (under (under ha2 X) Y)
    have hh4 : Derives Ω (SyntaxIndexLiftSyntax.lifted w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc u.castSucc.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise,SyntaxIndexLiftSyntax.lifted_rename]) (under (under hh2 X) Y)
    have hp4 : Derives Ω (value j.val (f j).val r.castSucc.castSucc.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise,value_rename]) (under (under hp2 X) Y)
    have hX4 : Derives Ω ((SyntaxNumeralSyntax.numeral j.val (Fin.last (m+2)).castSucc).conj
        (OmegaSyntax.successor (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc)) :=
      of_eq (by simp only [X,Formula.raise,Formula.rename,SyntaxNumeralSyntax.numeral_rename,successor_rename]) (under hX Y)
    have hedge := value_at _ _ _ _ _ hp4 (.conjL hX4) (.conjL hY)
    have ho := Derives.impE (.conjR (SyntaxIndexLiftEdges.successor_iff hZ4 _ _ _ _ _ _ _ _ _ _ _ hw4 hh4
      (member hZ4 j _ _ ha4 (.conjL hX4)) (.conjR hX4) (.conjR hY))) hedge
    exact of_eq (by simp only [Formula.raise,edge_rename]) ho

private def single (n : Nat) : Fin n → Fin (n+1) := fun j => ⟨j.val+1,by omega⟩
private def double (n : Nat) : Fin n → Fin (n+2) := fun j => ⟨j.val+2,by omega⟩

private theorem unary_lift (n : Nat) : YesMetaZFC.SetTheory.BoundEmbedding.lift (double n) =
    (YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderTwo : Fin (n+1) → Fin (n+3)) := by
  funext j
  refine Fin.cases rfl (fun k => ?_) j
  apply Fin.ext
  rfl

private theorem binary_one_lift (n : Nat) : YesMetaZFC.SetTheory.BoundEmbedding.lift
    (YesMetaZFC.SetTheory.BoundEmbedding.lift (single n)) =
    (YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne : Fin (n+2) → Fin (n+3)) := by
  funext j
  refine Fin.cases rfl (fun k => ?_) j
  refine Fin.cases rfl (fun k => ?_) k
  apply Fin.ext
  rfl

private theorem binary_two_lift (n : Nat) : YesMetaZFC.SetTheory.BoundEmbedding.lift
    (YesMetaZFC.SetTheory.BoundEmbedding.lift (double n)) =
    (YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo : Fin (n+2) → Fin (n+4)) := by
  funext j
  refine Fin.cases rfl (fun k => ?_) j
  refine Fin.cases rfl (fun k => ?_) k
  apply Fin.ext
  rfl

/-- The ACTUAL site-0 graph, not a replacement map, has the exact original
unaryUnderTwo values at every original input position. -/
theorem separation_value {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w count g : Fin m) (scopes : Fin 4 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxNumeralSyntax.numeral n count))
    (hg : Derives Γ (SchemaIndexSyntax.graph 0 w count scopes g)) (j : Fin (n+1)) :
    Derives Γ (value j.val (YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderTwo j).val g) := by
  let B := SchemaIndexSyntax.body 0 w count scopes g
  let Δ := Context.add B (HornBinderSyntax.raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ hg
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ B
  have hw2 : Derives Δ (omega (HornBinderSyntax.old 2 w)) :=
    of_eq (omega_rename w (HornBinderSyntax.old 2)) (HornBinderRules.under_body 2 hw B)
  have hn2 : Derives Δ (SyntaxNumeralSyntax.numeral n (HornBinderSyntax.old 2 count)) :=
    of_eq (SyntaxNumeralSyntax.numeral_rename n count (HornBinderSyntax.old 2)) (HornBinderRules.under_body 2 hn B)
  have hd (i : Fin n) : Derives Δ (value i.val (double n i).val (HornBinderSyntax.slot 2 0)) :=
    double_value hZ2 _ _ _ _ _ hw2 hn2 (.conjL hB) i
  have ho := lift_value hZ2 (double n) _ _ _ _ _ _ _ hw2 hn2 (.conjR (.conjR hB)) hd j
  rw [unary_lift] at ho
  exact of_eq (value_rename _ _ g (HornBinderSyntax.old 2)).symm ho

/-- The ACTUAL first Collection matrix graph preserves both original newest
variables and implements binaryUnderOne on every parameter position. -/
theorem collection_one_value {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w count g : Fin m) (scopes : Fin 4 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxNumeralSyntax.numeral n count))
    (hc : Derives Γ (SchemaIndexSyntax.chain count scopes))
    (hg : Derives Γ (SchemaIndexSyntax.graph 1 w count scopes g)) (j : Fin (n+2)) :
    Derives Γ (value j.val (YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne j).val g) := by
  let B := SchemaIndexSyntax.body 1 w count scopes g
  let Δ := Context.add B (HornBinderSyntax.raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ hg
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ B
  have hw2 : Derives Δ (omega (HornBinderSyntax.old 2 w)) :=
    of_eq (omega_rename w (HornBinderSyntax.old 2)) (HornBinderRules.under_body 2 hw B)
  have hn2 : Derives Δ (SyntaxNumeralSyntax.numeral n (HornBinderSyntax.old 2 count)) :=
    of_eq (SyntaxNumeralSyntax.numeral_rename n count (HornBinderSyntax.old 2)) (HornBinderRules.under_body 2 hn B)
  have hc2 : Derives Δ (SchemaIndexSyntax.chain (HornBinderSyntax.old 2 count) (fun i => HornBinderSyntax.old 2 (scopes i))) :=
    of_eq (SchemaIndexSyntax.chain_rename count scopes (HornBinderSyntax.old 2)) (HornBinderRules.under_body 2 hc B)
  have ha0 : Derives Δ (SyntaxNumeralSyntax.numeral (n+1) (HornBinderSyntax.old 2 (scopes 0))) :=
    SyntaxNumeralSyntax.intro_succ n _ _ hn2 (.conjL hc2)
  have hs (i : Fin n) : Derives Δ (value i.val (single n i).val (HornBinderSyntax.slot 2 0)) :=
    shift_value hZ2 _ _ _ _ hn2 (.conjL hB) i
  have hl (i : Fin (n+1)) : Derives Δ (value i.val (YesMetaZFC.SetTheory.BoundEmbedding.lift (single n) i).val (HornBinderSyntax.slot 2 1)) :=
    lift_value hZ2 (single n) _ _ _ _ _ _ _ hw2 hn2 (.conjL (.conjR hB)) hs i
  have ho := lift_value hZ2 (YesMetaZFC.SetTheory.BoundEmbedding.lift (single n)) _ _ _ _ _ _ _
    hw2 ha0 (.conjR (.conjR hB)) hl j
  rw [binary_one_lift] at ho
  exact of_eq (value_rename _ _ g (HornBinderSyntax.old 2)).symm ho

/-- The ACTUAL second Collection matrix graph implements the distinct
binaryUnderTwo embedding; it is not identified with the first matrix. -/
theorem collection_two_value {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w count g : Fin m) (scopes : Fin 4 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxNumeralSyntax.numeral n count))
    (hc : Derives Γ (SchemaIndexSyntax.chain count scopes))
    (hg : Derives Γ (SchemaIndexSyntax.graph 2 w count scopes g)) (j : Fin (n+2)) :
    Derives Γ (value j.val (YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo j).val g) := by
  let B := SchemaIndexSyntax.body 2 w count scopes g
  let Δ := Context.add B (HornBinderSyntax.raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ hg
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ B
  have hw2 : Derives Δ (omega (HornBinderSyntax.old 2 w)) :=
    of_eq (omega_rename w (HornBinderSyntax.old 2)) (HornBinderRules.under_body 2 hw B)
  have hn2 : Derives Δ (SyntaxNumeralSyntax.numeral n (HornBinderSyntax.old 2 count)) :=
    of_eq (SyntaxNumeralSyntax.numeral_rename n count (HornBinderSyntax.old 2)) (HornBinderRules.under_body 2 hn B)
  have hc2 : Derives Δ (SchemaIndexSyntax.chain (HornBinderSyntax.old 2 count) (fun i => HornBinderSyntax.old 2 (scopes i))) :=
    of_eq (SchemaIndexSyntax.chain_rename count scopes (HornBinderSyntax.old 2)) (HornBinderRules.under_body 2 hc B)
  have ha0 : Derives Δ (SyntaxNumeralSyntax.numeral (n+1) (HornBinderSyntax.old 2 (scopes 0))) :=
    SyntaxNumeralSyntax.intro_succ n _ _ hn2 (.conjL hc2)
  have hd (i : Fin n) : Derives Δ (value i.val (double n i).val (HornBinderSyntax.slot 2 0)) :=
    double_value hZ2 _ _ _ _ _ hw2 hn2 (.conjL hB) i
  have hl (i : Fin (n+1)) : Derives Δ (value i.val (YesMetaZFC.SetTheory.BoundEmbedding.lift (double n) i).val (HornBinderSyntax.slot 2 1)) :=
    lift_value hZ2 (double n) _ _ _ _ _ _ _ hw2 hn2 (.conjL (.conjR hB)) hd i
  have ho := lift_value hZ2 (YesMetaZFC.SetTheory.BoundEmbedding.lift (double n)) _ _ _ _ _ _ _
    hw2 ha0 (.conjR (.conjR hB)) hl j
  rw [binary_two_lift] at ho
  exact of_eq (value_rename _ _ g (HornBinderSyntax.old 2)).symm ho

end PPAC.Migration.Internal.SchemaIndexQuotation
