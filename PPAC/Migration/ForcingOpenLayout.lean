import PPAC.Migration.ForcingOpenCode
import PPAC.Migration.Internal.NaturalAdditionMonotone
import PPAC.Migration.Internal.StructuralListTraceOrder
import PPAC.Migration.Internal.SyntaxVariableImageGraph

/-! The source forcing proof uses pointwise name assignments. Reuse original
identity, addition, Replacement graphs and variable-image/encoding backends to
put name slots first and fixed parameter slots afterwards. All counts/indices
remain internal, including nonstandard; this is not a new arithmetic backend. -/
namespace PPAC.Migration.ForcingOpenLayout
open Internal Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax ReplacementPredicates HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open NaturalAdditionSyntax (sum sum_rename)
open NaturalAdditionBounds (below below_rename)
set_option maxRecDepth 16384
attribute [local irreducible] NaturalRecursionSyntax.matrix

/-- The ORIGINAL addition relation, used by the original Replacement graph. -/
def matrix : Formula 4 := sum 0 1 2 3
private def parameters {m} (w b : Fin m) : Fin 2 → Fin m := Source.SetLanguage.args2 w b
private theorem parameters_up {m} (w b : Fin m) : paramsUp (parameters w b) = parameters w.castSucc b.castSucc := by
  funext i
  exact Fin.cases rfl (fun i => Fin.cases rfl (fun e => Fin.elim0 e) i) i
private theorem matrix_rel {m} (ρ : Fin 2 → Fin m) (i j : Fin m) :
    rel matrix ρ i j = sum (ρ 0) (ρ 1) i j := by
  have h0 : Fin.lastCases j (Fin.lastCases i ρ) (0 : Fin 4) = ρ 0 := by
    change Fin.lastCases j (Fin.lastCases i ρ) (0 : Fin 2).castSucc.castSucc = ρ 0
    simp only [Fin.lastCases_castSucc]
  have h1 : Fin.lastCases j (Fin.lastCases i ρ) (1 : Fin 4) = ρ 1 := by
    change Fin.lastCases j (Fin.lastCases i ρ) (1 : Fin 2).castSucc.castSucc = ρ 1
    simp only [Fin.lastCases_castSucc]
  have h2 : Fin.lastCases j (Fin.lastCases i ρ) (2 : Fin 4) = i := by
    change Fin.lastCases j (Fin.lastCases i ρ) (Fin.last 2).castSucc = i
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
  have h3 : Fin.lastCases j (Fin.lastCases i ρ) (3 : Fin 4) = j := Fin.lastCases_last
  simp only [rel, Source.SetLanguage.relation, matrix, sum_rename, h0, h1, h2, h3]

/-- Exact ORIGINAL identity graph on names, with its codomain extended to b+f. -/
def nameMap {m} (w b t r : Fin m) : Formula m :=
  (SyntaxIdentityMapSyntax.graph b r).conj (SyntaxIndexMapSyntax.indexMap w r b t)
/-- Exact ORIGINAL addition graph i↦b+i on the parameter domain f. -/
def offset {m} (w b f t s : Fin m) : Formula m :=
  (RelationGraphSyntax.functionGraph matrix (parameters w b) f s).conj (SyntaxIndexMapSyntax.indexMap w s f t)
theorem nameMap_rename {m l} (w b t r : Fin m) (v : Fin m → Fin l) :
    (nameMap w b t r).rename v = nameMap (v w) (v b) (v t) (v r) := by
  simp only [nameMap, Formula.rename, SyntaxIdentityMapSyntax.graph_rename, SyntaxIndexMapSyntax.indexMap_rename]
theorem offset_rename {m l} (w b f t s : Fin m) (v : Fin m → Fin l) :
    (offset w b f t s).rename v = offset (v w) (v b) (v f) (v t) (v s) := by
  simp only [offset, Formula.rename, RelationGraphSyntax.functionGraph_rename, SyntaxIndexMapSyntax.indexMap_rename]
  congr 2
  funext i
  exact Fin.cases rfl (fun i => Fin.cases rfl (fun e => Fin.elim0 e) i) i

private theorem member_below {m} {Γ : Context m} (t b i : Fin m)
    (ht : Derives Γ (OrdinalSyntax.transitiveSet t)) (hb : Derives Γ (below b t)) (hi : Derives Γ (.mem i b)) :
    Derives Γ (.mem i t) := by
  apply Derives.disjE hb
  · have he : Derives (Context.add (.equal b t) Γ) (.equal b t) := .hyp (Or.inl rfl)
    let P := Formula.mem i.castSucc (Fin.last m)
    have h0 : Derives (Context.add (.equal b t) Γ) (P.instantiate b) := of_eq
      (by simp only [P, Formula.instantiate, Formula.rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (add hi _)
    exact of_eq (by simp only [P, Formula.instantiate, Formula.rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.eqSubst P he h0)
  · exact .impE (.impE (OrdinalSyntax.transitiveSet_at t b i (add ht _)) (.hyp (Or.inl rfl))) (add hi _)

private theorem prefix_from_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f t r : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hf : Derives Γ (.mem f w))
    (hs : Derives Γ (sum w b f t)) (hr : Derives Γ (SyntaxIdentityMapSyntax.graph b r)) : Derives Γ (nameMap w b t r) := by
  have ht := ZFArithmetic.add_range hZ w b f t hw hb hs
  have hbounds := NaturalAdditionOrderLaws.bounds (ZFContext.arithmetic hZ) w b f t (ZFContext.recAdd hZ)
    (ZFContext.separation hZ NaturalAdditionBounds.matrix) (ZFContext.separation hZ NaturalAdditionCommutative.matrix)
    (ZFContext.separation hZ NaturalAdditionShift.matrix) (ZFContext.separation hZ NaturalAdditionZero.matrix) hw hb hf hs
  have htrans := Derives.conjL (NaturalOrderBasic.ordinal hZ w t hw ht)
  have hmap := SyntaxIdentityGraph.index_map w b r hb hr
  have hbounded : Derives Γ (SequenceSyntax.bounded r t) := by
    apply Derives.allI
    apply Derives.allI
    apply Derives.impI
    let E := edge r.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
    have he : Derives Δ E := .hyp (Or.inl rfl)
    have hb2 : Derives Δ (SequenceSyntax.bounded r.castSucc.castSucc b.castSucc.castSucc) := of_eq
      (by simp only [Formula.raise, SequenceSyntax.bounded_rename]) (OrderedPairElimination.under_two (.conjR (.conjR hmap)) E)
    have hi := Derives.impE (SequenceSyntax.bounded_at r.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hb2) he
    exact member_below t.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1))
      (of_eq (by simp only [Formula.raise, OrdinalSyntax.transitiveSet_rename]) (OrderedPairElimination.under_two htrans E))
      (of_eq (by simp only [Formula.raise, below_rename]) (OrderedPairElimination.under_two (.conjL hbounds) E)) hi
  exact .conjI hr (.conjI (.conjI hb ht) (.conjI (.conjL hr) hbounded))

private theorem sum_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b i : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hi : Derives Γ (.mem i w)) :
    Derives Γ (ReplacementPredicates.fiber matrix (parameters w b) i) := by
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc b.castSucc i.castSucc (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ZFArithmetic.add_exists hZ w b i hw hb hi)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw T)
  have hi1 : Derives Δ (.mem i.castSucc w.castSucc) := under hi T
  have hu : Derives Δ (ReplacementPredicates.unique matrix (parameters w.castSucc b.castSucc) i.castSucc (Fin.last m)) := by
    simp only [ReplacementPredicates.unique, matrix_rel, parameters, paramsUp, PairSyntax.args2_first, PairSyntax.args2_second]
    apply Derives.allI
    apply Derives.impI
    let U := sum w.castSucc.castSucc b.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))
    let Ξ := Context.add U (Context.image Formula.raise Δ)
    exact ZFArithmetic.add_unique (ZFContext.under (ZFContext.under hZ T) U)
      w.castSucc.castSucc b.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc
      (of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 U)) (under hi1 U) (.hyp (Or.inl rfl))
      (of_eq (sum_rename w.castSucc b.castSucc i.castSucc (Fin.last m) Fin.castSucc) (under (.conjR hT) U))
  have hrel : Derives Δ (rel matrix (parameters w.castSucc b.castSucc) i.castSucc (Fin.last m)) :=
    of_eq (matrix_rel _ _ _).symm (.conjR hT)
  have ho : Derives Δ (ReplacementPredicates.fiber matrix (parameters w.castSucc b.castSucc) i.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, rel_rename, ReplacementPredicates.unique_rename,
      paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hrel hu)
  have e := (ReplacementPredicates.fiber_rename matrix (parameters w b) i Fin.castSucc).trans
    (congrArg (fun p => ReplacementPredicates.fiber matrix p i.castSucc) (parameters_up w b))
  exact of_eq e.symm ho

private theorem offset_total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hf : Derives Γ (.mem f w)) :
    Derives Γ (ReplacementPredicates.total matrix (parameters w b) f) := by
  apply Derives.allI
  apply Derives.impI
  let E := Formula.mem (Fin.last m) f.castSucc
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hi := StructuralListTraceOrder.member_member (ZFContext.under hZ E) w.castSucc (Fin.last m) f.castSucc hw1 (under hf E) (.hyp (Or.inl rfl))
  have h := sum_fiber (ZFContext.under hZ E) w.castSucc b.castSucc (Fin.last m) hw1 (under hb E) hi
  simpa only [parameters_up] using h

private theorem offset_outputs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f t : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hf : Derives Γ (.mem f w))
    (hs : Derives Γ (sum w b f t)) : Derives Γ (RelationGraph.outputsInto matrix (parameters w b) f t) := by
  simp only [RelationGraph.outputsInto, matrix_rel, parameters, paramsUp, PairSyntax.args2_first, PairSyntax.args2_second]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let E := (Formula.mem (Fin.last m).castSucc f.castSucc.castSucc).conj
    (sum w.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  have he : Derives Δ E := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under_two hZ E
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (OrderedPairElimination.under_two hw E)
  have hb2 : Derives Δ (.mem b.castSucc.castSucc w.castSucc.castSucc) := OrderedPairElimination.under_two hb E
  have hf2 : Derives Δ (.mem f.castSucc.castSucc w.castSucc.castSucc) := OrderedPairElimination.under_two hf E
  have hi := StructuralListTraceOrder.member_member hZ2 w.castSucc.castSucc (Fin.last m).castSucc f.castSucc.castSucc hw2 hf2 (.conjL he)
  have hs2 : Derives Δ (sum w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc t.castSucc.castSucc) := of_eq (by simp only [Formula.raise, sum_rename]) (OrderedPairElimination.under_two hs E)
  exact .impE (.conjL (NaturalAdditionMonotone.left_strict_iff hZ2 w.castSucc.castSucc (Fin.last m).castSucc f.castSucc.castSucc
    b.castSucc.castSucc (Fin.last (m+1)) t.castSucc.castSucc hw2 hi hf2 hb2 (.conjR he) hs2)) (.conjL he)

def existsNames {m} (w b t : Fin m) : Formula m := .ex (nameMap w.castSucc b.castSucc t.castSucc (Fin.last m))
def existsOffset {m} (w b f t : Fin m) : Formula m := .ex (offset w.castSucc b.castSucc f.castSucc t.castSucc (Fin.last m))
theorem existsNames_rename {m l} (w b t : Fin m) (v : Fin m → Fin l) :
    (existsNames w b t).rename v = existsNames (v w) (v b) (v t) := by
  simp only [existsNames, Formula.rename, nameMap_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem existsOffset_rename {m l} (w b f t : Fin m) (v : Fin m → Fin l) :
    (existsOffset w b f t).rename v = existsOffset (v w) (v b) (v f) (v t) := by
  simp only [existsOffset, Formula.rename, offset_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem names_total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f t : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hf : Derives Γ (.mem f w)) (hs : Derives Γ (sum w b f t)) :
    Derives Γ (existsNames w b t) := by
  let T := SyntaxIdentityMapSyntax.graph b.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (SyntaxIdentityGraph.exists_graph hZ b)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hp := prefix_from_graph (ZFContext.under hZ T) w.castSucc b.castSucc f.castSucc t.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw T)) (under hb T) (under hf T)
    (of_eq (sum_rename w b f t Fin.castSucc) (under hs T)) hT
  have out : Derives Δ (existsNames w.castSucc b.castSucc t.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, nameMap_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hp
  exact of_eq (existsNames_rename w b t Fin.castSucc).symm out

private theorem offset_from_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f t r : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hf : Derives Γ (.mem f w)) (hs : Derives Γ (sum w b f t))
    (hr : Derives Γ (RelationGraphSyntax.functionGraph matrix (parameters w b) f r)) : Derives Γ (offset w b f t r) := by
  have ht := ZFArithmetic.add_range hZ w b f t hw hb hs
  exact .conjI hr (.conjI (.conjI hf ht)
    (RelationGraph.sequence matrix (parameters w b) f t r hr (offset_outputs hZ w b f t hw hb hf hs)))

theorem offset_total_map {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f t : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hf : Derives Γ (.mem f w)) (hs : Derives Γ (sum w b f t)) :
    Derives Γ (existsOffset w b f t) := by
  let T := RelationGraphSyntax.functionGraph matrix (parameters w.castSucc b.castSucc) f.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  have he : Derives Γ (.ex T) := of_eq (by simp only [T, RelationGraphSyntax.existsGraph, parameters_up])
    (RelationGraphFunction.exists_graph hZ matrix (parameters w b) f (offset_total hZ w b f hw hb hf))
  apply Derives.exE (p := T) he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hp := offset_from_graph (ZFContext.under hZ T) w.castSucc b.castSucc f.castSucc t.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw T)) (under hb T) (under hf T)
    (of_eq (sum_rename w b f t Fin.castSucc) (under hs T)) hT
  have out : Derives Δ (existsOffset w.castSucc b.castSucc f.castSucc t.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, offset_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hp
  exact of_eq (existsOffset_rename w b f t Fin.castSucc).symm out

/-- Both actual full index graphs on the same original internal b+f. -/
def indices {m} (w b f t r s : Fin m) : Formula m := (sum w b f t).conj ((nameMap w b t r).conj (offset w b f t s))
theorem indices_rename {m l} (w b f t r s : Fin m) (v : Fin m → Fin l) :
    (indices w b f t r s).rename v = indices (v w) (v b) (v f) (v t) (v r) (v s) := by
  simp only [indices, Formula.rename, sum_rename, nameMap_rename, offset_rename]
private def indicesBody {m} (w b f t : Fin m) : Formula (m+2) :=
  indices (old 2 w) (old 2 b) (old 2 f) (old 2 t) (slot 2 0) (slot 2 1)
def existsIndices {m} (w b f t : Fin m) : Formula m := existsMany 2 (indicesBody w b f t)
theorem existsIndices_rename {m l} (w b f t : Fin m) (v : Fin m → Fin l) :
    (existsIndices w b f t).rename v = existsIndices (v w) (v b) (v f) (v t) := by
  simp only [existsIndices, existsMany_rename, indicesBody, indices_rename, lift_old, lift_slot]
private theorem intro_indices {m} {Γ : Context m} (w b f t r s : Fin m)
    (h : Derives Γ (indices w b f t r s)) : Derives Γ (existsIndices w b f t) := by
  apply HornBinderRules.intro_many 2 (indicesBody w b f t) (SyntaxAtomSyntax.two r s)
  exact of_eq (by simp only [indicesBody, indices_rename, assign_old, assign_slot]; rfl) h

theorem indices_total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f t : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hf : Derives Γ (.mem f w)) (hs : Derives Γ (sum w b f t)) :
    Derives Γ (existsIndices w b f t) := by
  let T := nameMap w.castSucc b.castSucc t.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (names_total hZ w b f t hw hb hf hs)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw T)
  have hs1 := of_eq (sum_rename w b f t Fin.castSucc) (under hs T)
  let U := offset w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc t.castSucc.castSucc (Fin.last (m+1))
  let Ξ := Context.add U (Context.image Formula.raise Δ)
  have outer : Derives Δ (existsIndices w.castSucc b.castSucc f.castSucc t.castSucc) := by
    apply Derives.exE (p := U) (offset_total_map (ZFContext.under hZ T) w.castSucc b.castSucc f.castSucc t.castSucc hw1 (under hb T) (under hf T) hs1)
    have hU : Derives Ξ U := .hyp (Or.inl rfl)
    have out := intro_indices w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
      (.conjI (of_eq (sum_rename w.castSucc b.castSucc f.castSucc t.castSucc Fin.castSucc) (under hs1 U))
        (.conjI (of_eq (nameMap_rename w.castSucc b.castSucc t.castSucc (Fin.last m) Fin.castSucc) (under hT U)) hU))
    exact of_eq (existsIndices_rename w.castSucc b.castSucc f.castSucc t.castSucc Fin.castSucc).symm out
  exact of_eq (existsIndices_rename w b f t Fin.castSucc).symm outer

theorem indices_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f t r s R S : Fin m)
    (hi : Derives Γ (indices w b f t r s)) (hj : Derives Γ (indices w b f t R S)) :
    Derives Γ ((Formula.equal r R).conj (.equal s S)) :=
  .conjI (SyntaxIdentityGraph.unique_graph hZ b r R (.conjL (.conjL (.conjR hi))) (.conjL (.conjL (.conjR hj))))
    (RelationGraph.unique_graph hZ matrix (parameters w b) f s S (.conjL (.conjR (.conjR hi))) (.conjL (.conjR (.conjR hj))))

/-- The target free count is generated, not assumed to have an external value. -/
def existsLayout {m} (w b f : Fin m) : Formula m := .ex (existsIndices w.castSucc b.castSucc f.castSucc (Fin.last m))
theorem existsLayout_rename {m l} (w b f : Fin m) (v : Fin m → Fin l) :
    (existsLayout w b f).rename v = existsLayout (v w) (v b) (v f) := by
  simp only [existsLayout, Formula.rename, existsIndices_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem layout_total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hf : Derives Γ (.mem f w)) : Derives Γ (existsLayout w b f) := by
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc b.castSucc f.castSucc (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ZFArithmetic.add_exists hZ w b f hw hb hf)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hi := indices_total (ZFContext.under hZ T) w.castSucc b.castSucc f.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw T)) (under hb T) (under hf T) (.conjR hT)
  have out : Derives Δ (existsLayout w.castSucc b.castSucc f.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, existsIndices_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hi
  exact of_eq (existsLayout_rename w b f Fin.castSucc).symm out

private def four {m} (r s g h : Fin m) : Fin 4 → Fin m := Fin.cases r (Fin.cases s (SyntaxAtomSyntax.two g h))
private def envData {m} (w z b f t R S : Fin m) (v : Fin 4 → Fin m) : Formula m :=
  (indices w b f t (v 0) (v 1)).conj
    ((SyntaxVariableImageSyntax.mapped false w (v 0) b z t (v 2)).conj
      ((SyntaxVariableImageSyntax.mapped false w (v 1) f z t (v 3)).conj
        (SyntaxMixedImageCodeSyntax.encodings w (v 2) (v 3) b f z t R S)))
private theorem envData_rename {m l} (w z b f t R S : Fin m) (v : Fin 4 → Fin m) (p : Fin m → Fin l) :
    (envData w z b f t R S v).rename p = envData (p w) (p z) (p b) (p f) (p t) (p R) (p S) (fun i => p (v i)) := by
  simp only [envData, Formula.rename, indices_rename, SyntaxVariableImageSyntax.mapped_rename, SyntaxMixedImageCodeSyntax.encodings_rename]
private def envBody {m} (w z b f t R S : Fin m) : Formula (m+4) :=
  envData (old 4 w) (old 4 z) (old 4 b) (old 4 f) (old 4 t) (old 4 R) (old 4 S) (slot 4)

/-- Actual original bound/free substitution codes. Source bound names map to
fvar i; source free parameters map to fvar(b+i). All hidden graphs are actual
original Replacement / variable-code / structural-list graphs. -/
def environment {m} (w z b f t R S : Fin m) : Formula m := existsMany 4 (envBody w z b f t R S)
theorem environment_rename {m l} (w z b f t R S : Fin m) (p : Fin m → Fin l) :
    (environment w z b f t R S).rename p = environment (p w) (p z) (p b) (p f) (p t) (p R) (p S) := by
  simp only [environment, existsMany_rename, envBody, envData_rename, lift_old, lift_slot]
private def pairBody {m} (w z b f t : Fin m) : Formula (m+2) :=
  environment (old 2 w) (old 2 z) (old 2 b) (old 2 f) (old 2 t) (slot 2 0) (slot 2 1)
def existsEnvironment {m} (w z b f t : Fin m) : Formula m := existsMany 2 (pairBody w z b f t)
theorem existsEnvironment_rename {m l} (w z b f t : Fin m) (p : Fin m → Fin l) :
    (existsEnvironment w z b f t).rename p = existsEnvironment (p w) (p z) (p b) (p f) (p t) := by
  simp only [existsEnvironment, existsMany_rename, pairBody, environment_rename, lift_old, lift_slot]
private theorem intro_environment {m} {Γ : Context m} (w z b f t R S r s g h : Fin m)
    (hi : Derives Γ (indices w b f t r s))
    (hg : Derives Γ (SyntaxVariableImageSyntax.mapped false w r b z t g))
    (hh : Derives Γ (SyntaxVariableImageSyntax.mapped false w s f z t h))
    (he : Derives Γ (SyntaxMixedImageCodeSyntax.encodings w g h b f z t R S)) : Derives Γ (environment w z b f t R S) := by
  apply HornBinderRules.intro_many 4 (envBody w z b f t R S) (four r s g h)
  exact of_eq (by simp only [envBody, envData_rename, assign_old, assign_slot]; rfl) (.conjI hi (.conjI hg (.conjI hh he)))
private theorem intro_pair {m} {Γ : Context m} (w z b f t R S : Fin m)
    (he : Derives Γ (environment w z b f t R S)) : Derives Γ (existsEnvironment w z b f t) := by
  apply HornBinderRules.intro_many 2 (pairBody w z b f t) (SyntaxAtomSyntax.two R S)
  exact of_eq (by simp only [pairBody, environment_rename, assign_old, assign_slot]; rfl) he

private theorem environment_from_maps {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b f t r s g h : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (indices w b f t r s))
    (hg : Derives Γ (SyntaxVariableImageSyntax.mapped false w r b z t g))
    (hh : Derives Γ (SyntaxVariableImageSyntax.mapped false w s f z t h)) : Derives Γ (existsEnvironment w z b f t) := by
  have hmaps : Derives Γ (SyntaxTermImageSyntax.maps w g h b f z t) := .conjI (.conjL (.conjR hg)) (.conjL (.conjR hh))
  have hc := SyntaxMixedImageCodePairs.exists_codes hZ w g h b f z t hw hmaps
  let T := SyntaxMixedImageCodePairs.codeBody w g h b f z t
  let Δ := Context.add T (raisedContext 2 Γ)
  change Derives Γ (existsMany 2 T) at hc
  apply HornBinderRules.eliminate_many 2 T _ hc
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hi2 := of_eq (indices_rename w b f t r s (old 2)) (add (HornBinderRules.under_many 2 hi) T)
  have hg2 := of_eq (SyntaxVariableImageSyntax.mapped_rename false w r b z t g (old 2)) (add (HornBinderRules.under_many 2 hg) T)
  have hh2 := of_eq (SyntaxVariableImageSyntax.mapped_rename false w s f z t h (old 2)) (add (HornBinderRules.under_many 2 hh) T)
  have he : Derives Δ (environment (old 2 w) (old 2 z) (old 2 b) (old 2 f) (old 2 t) (slot 2 0) (slot 2 1)) :=
    intro_environment (old 2 w) (old 2 z) (old 2 b) (old 2 f) (old 2 t) (slot 2 0) (slot 2 1)
      (old 2 r) (old 2 s) (old 2 g) (old 2 h) hi2 hg2 hh2 hT
  exact of_eq (existsEnvironment_rename w z b f t (old 2)).symm
    (intro_pair (old 2 w) (old 2 z) (old 2 b) (old 2 f) (old 2 t) (slot 2 0) (slot 2 1) he)

private theorem environment_at_indices {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b f t r s : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (.mem z w)) (hi : Derives Γ (indices w b f t r s)) :
    Derives Γ (existsEnvironment w z b f t) := by
  have hname := Derives.conjL (.conjR hi)
  have hnameIndex := Derives.conjR hname
  have hoff := Derives.conjR (.conjR hi)
  have ht := Derives.conjR (.conjL hnameIndex)
  have hctx : Derives Γ (SyntaxTermSyntax.contexts w z t) := .conjI hz ht
  have hrIn : Derives Γ (SyntaxVariableImageSyntax.input false w r b z t) := .conjI hctx hnameIndex
  have hsIn : Derives Γ (SyntaxVariableImageSyntax.input false w s f z t) := .conjI hctx (.conjR hoff)
  let T := SyntaxVariableImageSyntax.mapped false w.castSucc r.castSucc b.castSucc z.castSucc t.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (SyntaxVariableImageGraph.exists_map hZ false w r b z t hw hrIn)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw T)
  have hi1 := of_eq (indices_rename w b f t r s Fin.castSucc) (under hi T)
  have hsIn1 := of_eq (SyntaxVariableImageSyntax.input_rename false w s f z t Fin.castSucc) (under hsIn T)
  let U := SyntaxVariableImageSyntax.mapped false w.castSucc.castSucc s.castSucc.castSucc f.castSucc.castSucc z.castSucc.castSucc t.castSucc.castSucc (Fin.last (m+1))
  let Ξ := Context.add U (Context.image Formula.raise Δ)
  have outer : Derives Δ (existsEnvironment w.castSucc z.castSucc b.castSucc f.castSucc t.castSucc) := by
    apply Derives.exE (p := U) (SyntaxVariableImageGraph.exists_map (ZFContext.under hZ T) false w.castSucc s.castSucc f.castSucc z.castSucc t.castSucc hw1 hsIn1)
    have hU : Derives Ξ U := .hyp (Or.inl rfl)
    have he := environment_from_maps (ZFContext.under (ZFContext.under hZ T) U)
      w.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc t.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
      (of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 U))
      (of_eq (indices_rename w.castSucc b.castSucc f.castSucc t.castSucc r.castSucc s.castSucc Fin.castSucc) (under hi1 U))
      (of_eq (SyntaxVariableImageSyntax.mapped_rename false w.castSucc r.castSucc b.castSucc z.castSucc t.castSucc (Fin.last m) Fin.castSucc) (under hT U)) hU
    exact of_eq (existsEnvironment_rename w.castSucc z.castSucc b.castSucc f.castSucc t.castSucc Fin.castSucc).symm he
  exact of_eq (existsEnvironment_rename w z b f t Fin.castSucc).symm outer

/-- Both real variable term-code tables and their original natural list codes
are generated from the original complete index layout; no environment is given. -/
theorem environment_total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b f t : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (.mem z w)) (hb : Derives Γ (.mem b w)) (hf : Derives Γ (.mem f w))
    (hs : Derives Γ (sum w b f t)) : Derives Γ (existsEnvironment w z b f t) := by
  let T := indicesBody w b f t
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ (indices_total hZ w b f t hw hb hf hs)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have he := environment_at_indices (ZFContext.add (HornBinderRules.zf_many 2 hZ) T) (old 2 w) (old 2 z) (old 2 b) (old 2 f) (old 2 t) (slot 2 0) (slot 2 1)
    (of_eq (omega_rename w (old 2)) (add (HornBinderRules.under_many 2 hw) T)) (add (HornBinderRules.under_many 2 hz) T) hT
  exact of_eq (existsEnvironment_rename w z b f t (old 2)).symm he

theorem environment_sum {m} {Γ : Context m} (w z b f t R S : Fin m)
    (he : Derives Γ (environment w z b f t R S)) : Derives Γ (sum w b f t) := by
  let E := envBody w z b f t R S
  let Δ := Context.add E (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 E _ he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact of_eq (sum_rename w b f t (old 4)).symm (.conjL (.conjL hE))

theorem environment_types {m} {Γ : Context m} (w z b f t R S : Fin m)
    (he : Derives Γ (environment w z b f t R S)) : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w b f z t R S) := by
  let E := envBody w z b f t R S
  let Δ := Context.add E (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 E _ he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hc : Derives Δ (SyntaxMixedImageCodeSyntax.encodings (old 4 w) (slot 4 2) (slot 4 3) (old 4 b) (old 4 f) (old 4 z) (old 4 t) (old 4 R) (old 4 S)) := .conjR (.conjR (.conjR hE))
  exact of_eq (SyntaxMixedImageCodeSyntax.termLists_rename w b f z t R S (old 4)).symm
    (.conjI (SyntaxMixedImageCodeFields.term_list _ _ _ _ _ _ (.conjL hc))
      (SyntaxMixedImageCodeFields.term_list _ _ _ _ _ _ (.conjR hc)))

private def fieldValue {m} (w L i j q : Fin m) : Formula m :=
  (StructuralListFieldSyntax.field w L i q).iff (SyntaxVariableSyntax.code false w j q)
private theorem fieldValue_rename {m l} (w L i j q : Fin m) (v : Fin m → Fin l) :
    (fieldValue w L i j q).rename v = fieldValue (v w) (v L) (v i) (v j) (v q) := by
  simp only [fieldValue, Formula.iff, Formula.rename, StructuralListFieldSyntax.field_rename, SyntaxVariableSyntax.code_rename]
private theorem field_at_index {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a z t g L i j q : Fin m)
    (hm : Derives Γ (SyntaxVariableImageSyntax.mapped false w r a z t g))
    (hc : Derives Γ (SyntaxMixedImageCodeSyntax.encoded w g a z t L))
    (hi : Derives Γ (.mem i a)) (he : Derives Γ (edge r i j)) : Derives Γ (fieldValue w L i j q) := by
  have hf := SyntaxMixedImageCodeFields.edges w g a z t L i q hc
  have hv := SyntaxVariableImageFields.at_index hZ false w r a z t g i j q hm he
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (add (.conjL hv) _) (.impE (add (.conjR hf) _) (.conjI (add hi _) (.hyp (Or.inl rfl))))
  · apply Derives.impI
    exact .conjR (.impE (add (.conjL hf) _) (.impE (add (.conjR hv) _) (.hyp (Or.inl rfl))))

/-- Every original bound-name slot becomes the same free-variable index. -/
theorem names_field {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b f t R S i q : Fin m)
    (he : Derives Γ (environment w z b f t R S)) (hi : Derives Γ (.mem i b)) :
    Derives Γ (fieldValue w R i i q) := by
  let E := envBody w z b f t R S
  let Δ := Context.add E (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 E _ he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hi4 : Derives Δ (.mem (old 4 i) (old 4 b)) := add (HornBinderRules.under_many 4 hi) E
  have hidx := Derives.conjL hE
  have hn := Derives.conjL (.conjR hidx)
  have hr : Derives Δ (SyntaxIdentityMapSyntax.graph (old 4 b) (slot 4 0)) := .conjL hn
  have hdiag := Derives.impE (.conjR (SyntaxIdentityGraph.edge_iff (old 4 b) (slot 4 0) (old 4 i) (old 4 i) hr)) (.conjI hi4 (.eqRefl _))
  have out := field_at_index (ZFContext.add (HornBinderRules.zf_many 4 hZ) E) (old 4 w) (slot 4 0) (old 4 b) (old 4 z) (old 4 t) (slot 4 2) (old 4 R) (old 4 i) (old 4 i) (old 4 q)
    (.conjL (.conjR hE)) (.conjL (.conjR (.conjR (.conjR hE)))) hi4 hdiag
  exact of_eq (fieldValue_rename w R i i q (old 4)).symm out

/-- Every original parameter slot i becomes the actual free index b+i. -/
theorem parameters_field {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b f t R S i j q : Fin m)
    (he : Derives Γ (environment w z b f t R S)) (hi : Derives Γ (.mem i f)) (hj : Derives Γ (sum w b i j)) :
    Derives Γ (fieldValue w S i j q) := by
  let E := envBody w z b f t R S
  let Δ := Context.add E (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 E _ he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hi4 : Derives Δ (.mem (old 4 i) (old 4 f)) := add (HornBinderRules.under_many 4 hi) E
  have hj4 := of_eq (sum_rename w b i j (old 4)) (add (HornBinderRules.under_many 4 hj) E)
  have hidx := Derives.conjL hE
  have hoff := Derives.conjR (.conjR hidx)
  have hg : Derives Δ (RelationGraphSyntax.functionGraph matrix (parameters (old 4 w) (old 4 b)) (old 4 f) (slot 4 1)) := .conjL hoff
  have hrel : Derives Δ (rel matrix (parameters (old 4 w) (old 4 b)) (old 4 i) (old 4 j)) := of_eq (matrix_rel _ _ _).symm hj4
  have hEdge := Derives.impE (.conjR (RelationGraphSyntax.law_at matrix (parameters (old 4 w) (old 4 b)) (old 4 f) (slot 4 1) (old 4 i) (old 4 j) (.conjR hg))) (.conjI hi4 hrel)
  have out := field_at_index (ZFContext.add (HornBinderRules.zf_many 4 hZ) E) (old 4 w) (slot 4 1) (old 4 f) (old 4 z) (old 4 t) (slot 4 3) (old 4 S) (old 4 i) (old 4 j) (old 4 q)
    (.conjL (.conjR (.conjR hE))) (.conjR (.conjR (.conjR (.conjR hE)))) hi4 hEdge
  exact of_eq (fieldValue_rename w S i j q (old 4)).symm out

private theorem envData_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b f t R S U V : Fin m)
    (v u : Fin 4 → Fin m) (hw : Derives Γ (omega w))
    (he : Derives Γ (envData w z b f t R S v)) (hu : Derives Γ (envData w z b f t U V u)) :
    Derives Γ ((Formula.equal R U).conj (.equal S V)) := by
  have hidx := indices_unique hZ w b f t (v 0) (v 1) (u 0) (u 1) (.conjL he) (.conjL hu)
  have hNameV := Derives.conjL (.conjR he)
  have hNameU := SyntaxVariableImageFields.mapped_subst_index_graph false w (u 0) b z t (u 2) (v 0) (eq_symm (.conjL hidx)) (.conjL (.conjR hu))
  have hNames := SyntaxVariableImageGraph.unique hZ false w (v 0) b z t (v 2) (u 2) hNameV hNameU
  have hParamV := Derives.conjL (.conjR (.conjR he))
  have hParamU := SyntaxVariableImageFields.mapped_subst_index_graph false w (u 1) f z t (u 3) (v 1) (eq_symm (.conjR hidx)) (.conjL (.conjR (.conjR hu)))
  have hParams := SyntaxVariableImageGraph.unique hZ false w (v 1) f z t (v 3) (u 3) hParamV hParamU
  have hCodesV := Derives.conjR (.conjR (.conjR he))
  have hCodesU := Derives.conjR (.conjR (.conjR hu))
  have hRU := SyntaxMixedImageCodeUnique.subst_graph w (u 2) b z t U (v 2) (eq_symm hNames) (.conjL hCodesU)
  have hSV := SyntaxMixedImageCodeUnique.subst_graph w (u 3) f z t V (v 3) (eq_symm hParams) (.conjR hCodesU)
  exact .conjI (SyntaxMixedImageCodeUnique.unique_code hZ w (v 2) b z t R U hw (.conjL hCodesV) hRU)
    (SyntaxMixedImageCodeUnique.unique_code hZ w (v 3) f z t S V hw (.conjR hCodesV) hSV)

/-- Independent actual environment executions have the same original codes. -/
theorem environment_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b f t R S U V : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (environment w z b f t R S)) (hu : Derives Γ (environment w z b f t U V)) :
    Derives Γ ((Formula.equal R U).conj (.equal S V)) := by
  let E := envBody w z b f t R S
  let Δ := Context.add E (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 E _ he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hu4 := of_eq (environment_rename w z b f t U V (old 4)) (add (HornBinderRules.under_many 4 hu) E)
  have hw4 := of_eq (omega_rename w (old 4)) (add (HornBinderRules.under_many 4 hw) E)
  let F := envBody (old 4 w) (old 4 z) (old 4 b) (old 4 f) (old 4 t) (old 4 U) (old 4 V)
  let Ξ := Context.add F (raisedContext 4 Δ)
  have outer : Derives Δ ((Formula.equal (old 4 R) (old 4 U)).conj (.equal (old 4 S) (old 4 V))) := by
    apply HornBinderRules.eliminate_many 4 F _ hu4
    have hF : Derives Ξ F := .hyp (Or.inl rfl)
    have hE8 := of_eq (envData_rename (old 4 w) (old 4 z) (old 4 b) (old 4 f) (old 4 t) (old 4 R) (old 4 S) (slot 4) (old 4))
      (add (HornBinderRules.under_many 4 hE) F)
    exact envData_unique (ZFContext.add (HornBinderRules.zf_many 4 (ZFContext.add (HornBinderRules.zf_many 4 hZ) E)) F)
      (old 4 (old 4 w)) (old 4 (old 4 z)) (old 4 (old 4 b)) (old 4 (old 4 f)) (old 4 (old 4 t))
      (old 4 (old 4 R)) (old 4 (old 4 S)) (old 4 (old 4 U)) (old 4 (old 4 V))
      (fun i => old 4 (slot 4 i)) (slot 4)
      (of_eq (omega_rename (old 4 w) (old 4)) (add (HornBinderRules.under_many 4 hw4) F)) hE8 hF
  exact outer

def completeEnvironment {m} (w z b f : Fin m) : Formula m := .ex
  (existsEnvironment w.castSucc z.castSucc b.castSucc f.castSucc (Fin.last m))
theorem completeEnvironment_rename {m l} (w z b f : Fin m) (v : Fin m → Fin l) :
    (completeEnvironment w z b f).rename v = completeEnvironment (v w) (v z) (v b) (v f) := by
  simp only [completeEnvironment, Formula.rename, existsEnvironment_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem complete_environment_total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b f : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (.mem z w)) (hb : Derives Γ (.mem b w)) (hf : Derives Γ (.mem f w)) :
    Derives Γ (completeEnvironment w z b f) := by
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc b.castSucc f.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (ZFArithmetic.add_exists hZ w b f hw hb hf)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have he := environment_total (ZFContext.under hZ E) w.castSucc z.castSucc b.castSucc f.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw E)) (under hz E) (under hb E) (under hf E) (.conjR hE)
  have out : Derives Δ (completeEnvironment w.castSucc z.castSucc b.castSucc f.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, existsEnvironment_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) he
  exact of_eq (completeEnvironment_rename w z b f Fin.castSucc).symm out

def sentence {m} (w z b f : Fin m) : Source.Sentence :=
  ((omega w).imp ((empty z).imp ((Formula.mem b w).imp ((Formula.mem f w).imp (completeEnvironment w z b f))))).close
theorem kernel_certificate {m} (w z b f : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence w z b f)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Γ := Context.add (Formula.mem f w) (Context.add (Formula.mem b w) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Γ := ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _
  have hw : Derives Γ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hz : Derives Γ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  exact complete_environment_total hZ w z b f hw (OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingOpenLayout
