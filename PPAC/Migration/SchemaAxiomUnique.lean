/- Compose EXISTING component uniqueness for the actual original schema
pipeline. Internal witnesses remain arbitrary; no chosen/canonical map or output
is assumed and no component arithmetic/recursion/renamer is rebuilt. -/
import PPAC.Migration.SchemaShellTyping
import PPAC.Migration.Internal.SyntaxIdentityUnique
import PPAC.Migration.Internal.SyntaxFreeShiftGraph

namespace PPAC.Migration.SchemaAxiomUnique
open Source SourceAlgebra SourceLogic OmegaSyntax
open PPAC.Migration.Internal
open PPAC.Migration.Internal.HornBinderSyntax
open PPAC.Migration.Internal.SchemaIndexSyntax
open PPAC.Migration.Internal.SyntaxRenameQuerySyntax (of_eq)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
attribute [local irreducible] NaturalRecursionSyntax.matrix

private theorem lifted_input_subst {m} {Γ : Context m} (w r t a c u v g : Fin m)
    (he : Derives Γ (.equal r t)) (h : Derives Γ (SyntaxIndexLiftSyntax.lifted w r a c u v g)) :
    Derives Γ (SyntaxIndexLiftSyntax.lifted w t a c u v g) := by
  let P := SyntaxIndexLiftSyntax.lifted w.castSucc (Fin.last m) a.castSucc c.castSucc u.castSucc v.castSucc g.castSucc
  have h0 : P.instantiate r = SyntaxIndexLiftSyntax.lifted w r a c u v g := by
    simp only [P,Formula.instantiate,SyntaxIndexLiftSyntax.lifted_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate t = SyntaxIndexLiftSyntax.lifted w t a c u v g := by
    simp only [P,Formula.instantiate,SyntaxIndexLiftSyntax.lifted_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm h))

private theorem matrix_graph_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (site : Fin 3)
    (w n g h : Fin m) (scopes : Fin 4 → Fin m) (xs ys : Fin 2 → Fin m)
    (hx : Derives Γ (SchemaIndexSyntax.matrix site w n scopes g xs))
    (hy : Derives Γ (SchemaIndexSyntax.matrix site w n scopes h ys)) : Derives Γ (.equal g h) := by
  have cases : site = 0 ∨ site = 1 ∨ site = 2 := by omega
  rcases cases with rfl | rfl | rfl
  · have he := SchemaDoubleShiftGraph.unique_map hZ w n (scopes 0) (scopes 1) (ys 0) (xs 0) (.conjL hy) (.conjL hx)
    have hl := lifted_input_subst w (ys 0) (xs 0) n (scopes 1) (scopes 0) (scopes 2) h he (.conjR (.conjR hy))
    exact SyntaxIndexLift.unique hZ w (xs 0) n (scopes 1) (scopes 0) (scopes 2) g h (.conjR (.conjR hx)) hl
  · have he := SyntaxFreeShiftGraph.unique_map hZ w n (scopes 0) (ys 0) (xs 0) (.conjL hy) (.conjL hx)
    have hl := lifted_input_subst w (ys 0) (xs 0) n (scopes 0) (scopes 0) (scopes 1) (ys 1) he (.conjL (.conjR hy))
    have he1 := SyntaxIndexLift.unique hZ w (xs 0) n (scopes 0) (scopes 0) (scopes 1) (ys 1) (xs 1) hl (.conjL (.conjR hx))
    have hh := lifted_input_subst w (ys 1) (xs 1) (scopes 0) (scopes 1) (scopes 1) (scopes 2) h he1 (.conjR (.conjR hy))
    exact SyntaxIndexLift.unique hZ w (xs 1) (scopes 0) (scopes 1) (scopes 1) (scopes 2) g h (.conjR (.conjR hx)) hh
  · have he := SchemaDoubleShiftGraph.unique_map hZ w n (scopes 0) (scopes 1) (ys 0) (xs 0) (.conjL hy) (.conjL hx)
    have hl := lifted_input_subst w (ys 0) (xs 0) n (scopes 1) (scopes 0) (scopes 2) (ys 1) he (.conjL (.conjR hy))
    have he1 := SyntaxIndexLift.unique hZ w (xs 0) n (scopes 1) (scopes 0) (scopes 2) (ys 1) (xs 1) hl (.conjL (.conjR hx))
    have hh := lifted_input_subst w (ys 1) (xs 1) (scopes 0) (scopes 2) (scopes 1) (scopes 3) h he1 (.conjR (.conjR hy))
    exact SyntaxIndexLift.unique hZ w (xs 1) (scopes 0) (scopes 2) (scopes 1) (scopes 3) g h (.conjR (.conjR hx)) hh

/-- All three actual original index graphs are independent of their witnesses. -/
theorem index_graph_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (site : Fin 3)
    (w n g h : Fin m) (scopes : Fin 4 → Fin m)
    (hg : Derives Γ (SchemaIndexSyntax.graph site w n scopes g)) (hh : Derives Γ (SchemaIndexSyntax.graph site w n scopes h)) :
    Derives Γ (.equal g h) := by
  let X := SchemaIndexSyntax.body site w n scopes g
  let Δ := Context.add X (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 X _ hg
  have hX : Derives Δ X := .hyp (Or.inl rfl)
  have hh2 := of_eq (SchemaIndexSyntax.graph_rename site w n scopes h (old 2)) (HornBinderRules.under_body 2 hh X)
  let Y := SchemaIndexSyntax.body site (old 2 w) (old 2 n) (fun i => old 2 (scopes i)) (old 2 h)
  let Ξ := Context.add Y (raisedContext 2 Δ)
  apply HornBinderRules.eliminate_many 2 Y _ hh2
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hx4 : Derives Ξ (SchemaIndexSyntax.matrix site (old 2 (old 2 w)) (old 2 (old 2 n))
      (fun i => old 2 (old 2 (scopes i))) (old 2 (old 2 g)) (fun i => old 2 (slot 2 i))) :=
    of_eq (by simp only [X,SchemaIndexSyntax.body,SchemaIndexSyntax.matrix_rename]) (HornBinderRules.under_body 2 hX Y)
  have he := matrix_graph_unique (HornBinderRules.zf_body 2 (HornBinderRules.zf_body 2 hZ X) Y) site
    (old 2 (old 2 w)) (old 2 (old 2 n)) (old 2 (old 2 g)) (old 2 (old 2 h)) (fun i => old 2 (old 2 (scopes i)))
    (fun i => old 2 (slot 2 i)) (slot 2) hx4 hY
  exact he

private theorem system_codes_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (site : Fin 3)
    (w n z g R S h T V : Fin m) (scopes : Fin 4 → Fin m) (hw : Derives Γ (omega w))
    (hx : Derives Γ (SchemaIndexRenameSystem.system site w n z scopes g R S))
    (hy : Derives Γ (SchemaIndexRenameSystem.system site w n z scopes h T V)) :
    Derives Γ ((Formula.equal R T).conj (.equal S V)) := by
  have he := index_graph_unique hZ site w n g h scopes (.conjR (.conjL (.conjL hx))) (.conjR (.conjL (.conjL hy)))
  have hr := SyntaxMapCodeSyntax.graph_subst w g h (sourceScope site scopes) (targetScope site scopes) R he (.conjR (.conjL hx))
  exact .conjI (SyntaxMapCode.unique_code hZ w h (sourceScope site scopes) (targetScope site scopes) R T hw hr (.conjR (.conjL hy)))
    (SyntaxIdentityUnique.code_unique hZ w z S V hw (.conjL (.conjR hx)) (.conjL (.conjR hy)))

private theorem rename_bound_subst {m} {Γ : Context m} (w R T S a z c input out : Fin m)
    (he : Derives Γ (.equal R T)) (h : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a z c z input out)) :
    Derives Γ (SyntaxRenameJudgmentSyntax.renamed w T S a z c z input out) := by
  let P := SyntaxRenameJudgmentSyntax.renamed w.castSucc (Fin.last m) S.castSucc a.castSucc z.castSucc c.castSucc z.castSucc input.castSucc out.castSucc
  have h0 : P.instantiate R = SyntaxRenameJudgmentSyntax.renamed w R S a z c z input out := by
    simp only [P,Formula.instantiate,SyntaxRenameJudgmentSyntax.renamed_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate T = SyntaxRenameJudgmentSyntax.renamed w T S a z c z input out := by
    simp only [P,Formula.instantiate,SyntaxRenameJudgmentSyntax.renamed_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm h))

private theorem rename_free_subst {m} {Γ : Context m} (w R S T a z c input out : Fin m)
    (he : Derives Γ (.equal S T)) (h : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a z c z input out)) :
    Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R T a z c z input out) := by
  let P := SyntaxRenameJudgmentSyntax.renamed w.castSucc R.castSucc (Fin.last m) a.castSucc z.castSucc c.castSucc z.castSucc input.castSucc out.castSucc
  have h0 : P.instantiate S = SyntaxRenameJudgmentSyntax.renamed w R S a z c z input out := by
    simp only [P,Formula.instantiate,SyntaxRenameJudgmentSyntax.renamed_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate T = SyntaxRenameJudgmentSyntax.renamed w R T a z c z input out := by
    simp only [P,Formula.instantiate,SyntaxRenameJudgmentSyntax.renamed_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm h))

private theorem at_systems {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (site : Fin 3)
    (w n z input x y g R S h T V : Fin m) (scopes : Fin 4 → Fin m) (hw : Derives Γ (omega w))
    (hx : Derives Γ (SchemaIndexRenameSystem.system site w n z scopes g R S))
    (hy : Derives Γ (SchemaIndexRenameSystem.system site w n z scopes h T V))
    (hxr : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S (sourceScope site scopes) z (targetScope site scopes) z input x))
    (hyr : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w T V (sourceScope site scopes) z (targetScope site scopes) z input y)) :
    Derives Γ (.equal x y) := by
  have he := system_codes_unique hZ site w n z g R S h T V scopes hw hx hy
  have hb := rename_bound_subst w R T S (sourceScope site scopes) z (targetScope site scopes) input x (.conjL he) hxr
  have hh := rename_free_subst w T S V (sourceScope site scopes) z (targetScope site scopes) input x (.conjR he) hb
  have hu := SyntaxRenameOutputClassify.unique_output_of_renamed hZ w T V (sourceScope site scopes) z (targetScope site scopes) z input x hw hh
  exact eq_symm (SyntaxRenameFiberUnique.at_unique w T V (sourceScope site scopes) z (targetScope site scopes) z input y x hu hyr)

/-- Actual renamed matrices agree even with independently generated graphs/codes. -/
theorem renamed_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (site : Fin 3)
    (w n z input x y : Fin m) (scopes : Fin 4 → Fin m) (hw : Derives Γ (omega w))
    (hx : Derives Γ (SchemaAxiomCompilation.renamedMatrix site w n z scopes input x))
    (hy : Derives Γ (SchemaAxiomCompilation.renamedMatrix site w n z scopes input y)) : Derives Γ (.equal x y) := by
  let X := SchemaAxiomCompilation.renamedBody site w n z scopes input x
  let Δ := Context.add X (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 X _ hx
  have hX : Derives Δ X := .hyp (Or.inl rfl)
  have hy3 := of_eq (SchemaAxiomCompilation.renamedMatrix_rename site w n z input y scopes (old 3)) (HornBinderRules.under_body 3 hy X)
  let Y := SchemaAxiomCompilation.renamedBody site (old 3 w) (old 3 n) (old 3 z) (fun i => old 3 (scopes i)) (old 3 input) (old 3 y)
  let Ξ := Context.add Y (raisedContext 3 Δ)
  apply HornBinderRules.eliminate_many 3 Y _ hy3
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hx6 : Derives Ξ ((SchemaIndexRenameSystem.system site (old 3 (old 3 w)) (old 3 (old 3 n)) (old 3 (old 3 z))
      (fun i => old 3 (old 3 (scopes i))) (old 3 (slot 3 0)) (old 3 (slot 3 1)) (old 3 (slot 3 2))).conj
    (SyntaxRenameJudgmentSyntax.renamed (old 3 (old 3 w)) (old 3 (slot 3 1)) (old 3 (slot 3 2))
      (sourceScope site (fun i => old 3 (old 3 (scopes i)))) (old 3 (old 3 z))
      (targetScope site (fun i => old 3 (old 3 (scopes i)))) (old 3 (old 3 z)) (old 3 (old 3 input)) (old 3 (old 3 x)))) := by
    simpa only [X,SchemaAxiomCompilation.renamedBody,Formula.rename,SchemaIndexRenameSystem.system_rename,
      SyntaxRenameJudgmentSyntax.renamed_rename,sourceScope_map,targetScope_map] using HornBinderRules.under_body 3 hX Y
  have hy6 : Derives Ξ ((SchemaIndexRenameSystem.system site (old 3 (old 3 w)) (old 3 (old 3 n)) (old 3 (old 3 z))
      (fun i => old 3 (old 3 (scopes i))) (slot 3 0) (slot 3 1) (slot 3 2)).conj
    (SyntaxRenameJudgmentSyntax.renamed (old 3 (old 3 w)) (slot 3 1) (slot 3 2)
      (sourceScope site (fun i => old 3 (old 3 (scopes i)))) (old 3 (old 3 z))
      (targetScope site (fun i => old 3 (old 3 (scopes i)))) (old 3 (old 3 z)) (old 3 (old 3 input)) (old 3 (old 3 y)))) := by
    simpa only [Y,SchemaAxiomCompilation.renamedBody,sourceScope_map,targetScope_map] using hY
  have hw6 : Derives Ξ (omega (old 3 (old 3 w))) := of_eq (by simp only [omega_rename])
    (HornBinderRules.under_body 3 (HornBinderRules.under_body 3 hw X) Y)
  have he := at_systems (HornBinderRules.zf_body 3 (HornBinderRules.zf_body 3 hZ X) Y) site
    (old 3 (old 3 w)) (old 3 (old 3 n)) (old 3 (old 3 z)) (old 3 (old 3 input)) (old 3 (old 3 x)) (old 3 (old 3 y))
    (old 3 (slot 3 0)) (old 3 (slot 3 1)) (old 3 (slot 3 2)) (slot 3 0) (slot 3 1) (slot 3 2)
    (fun i => old 3 (old 3 (scopes i))) hw6 (.conjL hx6) (.conjL hy6) (.conjR hx6) (.conjR hy6)
  exact he


private theorem matrix_input_subst {m} {Γ : Context m} (site : Fin 3) (w n z a b out : Fin m) (scopes : Fin 4 → Fin m)
    (he : Derives Γ (.equal a b)) (h : Derives Γ (SchemaAxiomCompilation.renamedMatrix site w n z scopes a out)) :
    Derives Γ (SchemaAxiomCompilation.renamedMatrix site w n z scopes b out) := by
  let P := SchemaAxiomCompilation.renamedMatrix site w.castSucc n.castSucc z.castSucc
    (fun i => (scopes i).castSucc) (Fin.last m) out.castSucc
  have h0 : P.instantiate a = SchemaAxiomCompilation.renamedMatrix site w n z scopes a out := by
    simp only [P,Formula.instantiate,SchemaAxiomCompilation.renamedMatrix_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate b = SchemaAxiomCompilation.renamedMatrix site w n z scopes b out := by
    simp only [P,Formula.instantiate,SchemaAxiomCompilation.renamedMatrix_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm h))

/-- One raw body, arbitrarily independent actual compilations and rename systems. -/
theorem compiled_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (site : Fin 3)
    (w n z body x y : Fin m) (scopes : Fin 4 → Fin m) (hw : Derives Γ (omega w))
    (hx : Derives Γ (SchemaAxiomCompilation.compiledMatrix site w n z body x scopes))
    (hy : Derives Γ (SchemaAxiomCompilation.compiledMatrix site w n z body y scopes)) : Derives Γ (.equal x y) := by
  let X := SchemaAxiomCompilation.compiledBody site w n z body x scopes
  let Δ := Context.add X (Context.image Formula.raise Γ)
  apply Derives.exE (p := X) hx
  have hX : Derives Δ X := .hyp (Or.inl rfl)
  have hy1 := of_eq (SchemaAxiomCompilation.compiledMatrix_rename site w n z body y scopes Fin.castSucc) (under hy X)
  let Y := SchemaAxiomCompilation.compiledBody site w.castSucc n.castSucc z.castSucc body.castSucc y.castSucc (fun i => (scopes i).castSucc)
  let Ξ := Context.add Y (Context.image Formula.raise Δ)
  apply Derives.exE (p := Y) hy1
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hx2 : Derives Ξ ((ProjectCompilerCodeSyntax.compiled w.castSucc.castSucc body.castSucc.castSucc
      (sourceScope site (fun i => (scopes i).castSucc.castSucc)) (Fin.last m).castSucc).conj
    (SchemaAxiomCompilation.renamedMatrix site w.castSucc.castSucc n.castSucc.castSucc z.castSucc.castSucc
      (fun i => (scopes i).castSucc.castSucc) (Fin.last m).castSucc x.castSucc.castSucc)) := by
    simpa only [X,SchemaAxiomCompilation.compiledBody,Formula.raise,Formula.rename,ProjectCompilerCodeSyntax.compiled_rename,
      SchemaAxiomCompilation.renamedMatrix_rename,sourceScope_map] using under hX Y
  have hy2 : Derives Ξ ((ProjectCompilerCodeSyntax.compiled w.castSucc.castSucc body.castSucc.castSucc
      (sourceScope site (fun i => (scopes i).castSucc.castSucc)) (Fin.last (m+1))).conj
    (SchemaAxiomCompilation.renamedMatrix site w.castSucc.castSucc n.castSucc.castSucc z.castSucc.castSucc
      (fun i => (scopes i).castSucc.castSucc) (Fin.last (m+1)) y.castSucc.castSucc)) := by
    simpa only [Y,SchemaAxiomCompilation.compiledBody,sourceScope_map] using hY
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise,omega_rename]) (under (under hw X) Y)
  have hZ2 := ZFContext.under (ZFContext.under hZ X) Y
  have he := ProjectCompilerUnique.unique_outputs hZ2 w.castSucc.castSucc body.castSucc.castSucc
    (sourceScope site (fun i => (scopes i).castSucc.castSucc)) (Fin.last m).castSucc (Fin.last (m+1)) hw2 (.conjL hx2) (.conjL hy2)
  have hr := matrix_input_subst site w.castSucc.castSucc n.castSucc.castSucc z.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    x.castSucc.castSucc (fun i => (scopes i).castSucc.castSucc) he (.conjR hx2)
  have hout := renamed_unique hZ2 site w.castSucc.castSucc n.castSucc.castSucc z.castSucc.castSucc (Fin.last (m+1))
    x.castSucc.castSucc y.castSucc.castSucc (fun i => (scopes i).castSucc.castSucc) hw2 hr (.conjR hy2)
  exact hout


private theorem assembled_slots_subst {m} {Γ : Context m} (collection : Bool) (w n out x u y v : Fin m)
    (hx : Derives Γ (.equal x u)) (hy : Derives Γ (.equal y v))
    (ha : Derives Γ (SchemaAxiomAssembly.assembled collection w n (fun i => if i.val = 0 then x else y) out)) :
    Derives Γ (SchemaAxiomAssembly.assembled collection w n (fun i => if i.val = 0 then u else v) out) := by
  let P := SchemaAxiomAssembly.assembled collection w.castSucc n.castSucc
    (fun i => if i.val = 0 then Fin.last m else y.castSucc) out.castSucc
  have h0 : P.instantiate x = SchemaAxiomAssembly.assembled collection w n (fun i => if i.val = 0 then x else y) out := by
    simp only [P,Formula.instantiate,SchemaAxiomAssembly.assembled_rename,apply_ite,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate u = SchemaAxiomAssembly.assembled collection w n (fun i => if i.val = 0 then u else y) out := by
    simp only [P,Formula.instantiate,SchemaAxiomAssembly.assembled_rename,apply_ite,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have ha1 := of_eq h1 (Derives.eqSubst P hx (of_eq h0.symm ha))
  let Q := SchemaAxiomAssembly.assembled collection w.castSucc n.castSucc
    (fun i => if i.val = 0 then u.castSucc else Fin.last m) out.castSucc
  have h2 : Q.instantiate y = SchemaAxiomAssembly.assembled collection w n (fun i => if i.val = 0 then u else y) out := by
    simp only [Q,Formula.instantiate,SchemaAxiomAssembly.assembled_rename,apply_ite,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h3 : Q.instantiate v = SchemaAxiomAssembly.assembled collection w n (fun i => if i.val = 0 then u else v) out := by
    simp only [Q,Formula.instantiate,SchemaAxiomAssembly.assembled_rename,apply_ite,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h3 (Derives.eqSubst Q hy (of_eq h2.symm ha1))

private theorem at_matrices {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (collection : Bool)
    (w n z body out other x y u v : Fin m) (scopes : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (Source.Formula.mem n w))
    (hx : Derives Γ (SchemaAxiomCompilation.compiledMatrix (SchemaAxiomCompilation.firstSite collection) w n z body x scopes))
    (hy : Derives Γ (if collection then SchemaAxiomCompilation.compiledMatrix 2 w n z body y scopes else Formula.equal y x))
    (hu : Derives Γ (SchemaAxiomCompilation.compiledMatrix (SchemaAxiomCompilation.firstSite collection) w n z body u scopes))
    (hv : Derives Γ (if collection then SchemaAxiomCompilation.compiledMatrix 2 w n z body v scopes else Formula.equal v u))
    (ha : Derives Γ (SchemaAxiomAssembly.assembled collection w n (fun i => if i.val = 0 then x else y) out))
    (hb : Derives Γ (SchemaAxiomAssembly.assembled collection w n (fun i => if i.val = 0 then u else v) other)) :
    Derives Γ (.equal out other) := by
  have hxu := compiled_unique hZ (SchemaAxiomCompilation.firstSite collection) w n z body x u scopes hw hx hu
  have hyv : Derives Γ (.equal y v) := by
    cases collection
    · exact eq_trans hy (eq_trans hxu (eq_symm hv))
    · exact compiled_unique hZ 2 w n z body y v scopes hw hy hv
  have ha1 := assembled_slots_subst collection w n out x u y v hxu hyv ha
  have huW := Derives.conjL (FormulaCodeProperties.guards _ _ _ _
    (SchemaAxiomCompilation.compiled_target_type (SchemaAxiomCompilation.firstSite collection) w n z body u scopes hu))
  have hvW : Derives Γ (Source.Formula.mem v w) := by
    cases collection
    · exact mem_subst (eq_symm hv) huW
    · exact .conjL (FormulaCodeProperties.guards _ _ _ _ (SchemaAxiomCompilation.compiled_target_type 2 w n z body v scopes hv))
  have henv : Derives Γ (HornExprSyntax.environmentNat 3 w (fun i => if i.val = 0 then u else v)) :=
    .conjI huW (.conjI hvW (.conjI hvW (.impI (.hyp (Or.inl rfl)))))
  exact SchemaAxiomAssembly.output_unique hZ collection w n out other (fun i => if i.val = 0 then u else v) hw hn henv ha1 hb

/-- Every pair of actual full pipeline outputs agrees; ALL internal witnesses
for compilation, graphs, codes, matrices, core and whole closure may differ. -/
theorem result_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (collection : Bool)
    (w n z body out other : Fin m) (scopes : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (Source.Formula.mem n w))
    (hx : Derives Γ (SchemaAxiomCompilation.schemaResult collection w n z body out scopes))
    (hy : Derives Γ (SchemaAxiomCompilation.schemaResult collection w n z body other scopes)) : Derives Γ (.equal out other) := by
  let X := SchemaAxiomCompilation.schemaBody collection w n z body out scopes
  let Δ := Context.add X (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 X _ hx
  have hX : Derives Δ X := .hyp (Or.inl rfl)
  have hy2 := of_eq (SchemaAxiomCompilation.schemaResult_rename collection w n z body other scopes (old 2)) (HornBinderRules.under_body 2 hy X)
  let Y := SchemaAxiomCompilation.schemaBody collection (old 2 w) (old 2 n) (old 2 z) (old 2 body) (old 2 other) (fun i => old 2 (scopes i))
  let Ξ := Context.add Y (raisedContext 2 Δ)
  apply HornBinderRules.eliminate_many 2 Y _ hy2
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  let ww := old 2 (old 2 w)
  let nn := old 2 (old 2 n)
  let zz := old 2 (old 2 z)
  let bb := old 2 (old 2 body)
  let ss := fun i => old 2 (old 2 (scopes i))
  let x : Fin (m+2+2) := old 2 (slot 2 0)
  let y : Fin (m+2+2) := old 2 (slot 2 1)
  let u : Fin (m+2+2) := slot 2 0
  let v : Fin (m+2+2) := slot 2 1
  have hx4 : Derives Ξ ((SchemaAxiomCompilation.compiledMatrix (SchemaAxiomCompilation.firstSite collection) ww nn zz bb x ss).conj
      ((if collection then SchemaAxiomCompilation.compiledMatrix 2 ww nn zz bb y ss else Formula.equal y x).conj
        (SchemaAxiomAssembly.assembled collection ww nn (fun i => if i.val = 0 then x else y) (old 2 (old 2 out))))) := by
    cases collection <;> simpa only [X,SchemaAxiomCompilation.schemaBody,Bool.false_eq_true,↓reduceIte,Formula.rename,
      SchemaAxiomCompilation.compiledMatrix_rename,SchemaAxiomAssembly.assembled_rename,apply_ite] using HornBinderRules.under_body 2 hX Y
  have hy4 : Derives Ξ ((SchemaAxiomCompilation.compiledMatrix (SchemaAxiomCompilation.firstSite collection) ww nn zz bb u ss).conj
      ((if collection then SchemaAxiomCompilation.compiledMatrix 2 ww nn zz bb v ss else Formula.equal v u).conj
        (SchemaAxiomAssembly.assembled collection ww nn (fun i => if i.val = 0 then u else v) (old 2 (old 2 other))))) := hY
  have hw4 : Derives Ξ (omega ww) := of_eq (by simp only [ww,omega_rename]) (HornBinderRules.under_body 2 (HornBinderRules.under_body 2 hw X) Y)
  have hn4 := HornBinderRules.under_body 2 (HornBinderRules.under_body 2 hn X) Y
  exact at_matrices (HornBinderRules.zf_body 2 (HornBinderRules.zf_body 2 hZ X) Y) collection ww nn zz bb
    (old 2 (old 2 out)) (old 2 (old 2 other)) x y u v ss hw4 hn4 (.conjL hx4) (.conjL (.conjR hx4))
    (.conjL hy4) (.conjL (.conjR hy4)) (.conjR (.conjR hx4)) (.conjR (.conjR hy4))

/-- The four actual successor-scope witnesses are themselves unique. -/
theorem scope_chain_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (n : Fin m) (xs ys : Fin 4 → Fin m)
    (hx : Derives Γ (SchemaIndexSyntax.chain n xs)) (hy : Derives Γ (SchemaIndexSyntax.chain n ys)) :
    ∀ i, Derives Γ (Formula.equal (xs i) (ys i)) := by
  have he := (ZFContext.arithmetic hZ).base.extensionality
  have h0 := OmegaUniversal.successor_unique (xs 0) (ys 0) n he (.conjL hx) (.conjL hy)
  have hy1 := NaturalAdditionTransport.successor_input_subst (ys 1) (ys 0) (xs 0) (eq_symm h0) (.conjL (.conjR hy))
  have h1 := OmegaUniversal.successor_unique (xs 1) (ys 1) (xs 0) he (.conjL (.conjR hx)) hy1
  have hy2 := NaturalAdditionTransport.successor_input_subst (ys 2) (ys 1) (xs 1) (eq_symm h1) (.conjL (.conjR (.conjR hy)))
  have h2 := OmegaUniversal.successor_unique (xs 2) (ys 2) (xs 1) he (.conjL (.conjR (.conjR hx))) hy2
  have hy3 := NaturalAdditionTransport.successor_input_subst (ys 3) (ys 2) (xs 2) (eq_symm h2) (.conjR (.conjR (.conjR hy)))
  have h3 := OmegaUniversal.successor_unique (xs 3) (ys 3) (xs 2) he (.conjR (.conjR (.conjR hx))) hy3
  intro i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

private theorem scope_at_subst {m} {Γ : Context m} (collection : Bool) (w n z body out a : Fin m) (scopes : Fin 4 → Fin m) (i : Fin 4)
    (he : Derives Γ (.equal (scopes i) a))
    (h : Derives Γ (SchemaAxiomCompilation.schemaResult collection w n z body out scopes)) :
    Derives Γ (SchemaAxiomCompilation.schemaResult collection w n z body out (fun j => if j = i then a else scopes j)) := by
  let P := SchemaAxiomCompilation.schemaResult collection w.castSucc n.castSucc z.castSucc body.castSucc out.castSucc
    (fun j => if j = i then Fin.last m else (scopes j).castSucc)
  have hs : (fun j => if j = i then scopes i else scopes j) = scopes := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [↓reduceIte]
    · simp only [if_neg hj]
  have h0 : P.instantiate (scopes i) = SchemaAxiomCompilation.schemaResult collection w n z body out scopes := by
    simp only [P,Formula.instantiate,SchemaAxiomCompilation.schemaResult_rename,apply_ite,
      Fin.lastCases_last,Fin.lastCases_castSucc,id_eq,hs]
  have h1 : P.instantiate a = SchemaAxiomCompilation.schemaResult collection w n z body out (fun j => if j = i then a else scopes j) := by
    simp only [P,Formula.instantiate,SchemaAxiomCompilation.schemaResult_rename,apply_ite,
      Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm h))

private theorem scopes_subst {m} {Γ : Context m} (collection : Bool) (w n z body out : Fin m) (xs ys : Fin 4 → Fin m)
    (he : ∀ i, Derives Γ (.equal (xs i) (ys i)))
    (h : Derives Γ (SchemaAxiomCompilation.schemaResult collection w n z body out xs)) :
    Derives Γ (SchemaAxiomCompilation.schemaResult collection w n z body out ys) := by
  let s0 := fun j => if j = (0 : Fin 4) then ys 0 else xs j
  let s1 := fun j => if j = (1 : Fin 4) then ys 1 else s0 j
  let s2 := fun j => if j = (2 : Fin 4) then ys 2 else s1 j
  let s3 := fun j => if j = (3 : Fin 4) then ys 3 else s2 j
  have h0 : Derives Γ (SchemaAxiomCompilation.schemaResult collection w n z body out s0) := scope_at_subst collection w n z body out (ys 0) xs 0 (he 0) h
  have h1 : Derives Γ (SchemaAxiomCompilation.schemaResult collection w n z body out s1) :=
    scope_at_subst collection w n z body out (ys 1) s0 1 (by change Derives Γ (.equal (xs 1) (ys 1)); exact he 1) h0
  have h2 : Derives Γ (SchemaAxiomCompilation.schemaResult collection w n z body out s2) :=
    scope_at_subst collection w n z body out (ys 2) s1 2 (by change Derives Γ (.equal (xs 2) (ys 2)); exact he 2) h1
  have h3 : Derives Γ (SchemaAxiomCompilation.schemaResult collection w n z body out s3) :=
    scope_at_subst collection w n z body out (ys 3) s2 3 (by change Derives Γ (.equal (xs 3) (ys 3)); exact he 3) h2
  have hs : s3 = ys := by
    funext i
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> rfl
  exact of_eq (congrArg (SchemaAxiomCompilation.schemaResult collection w n z body out) hs) h3

/-- Comparison also allows independently constructed successor-scope chains. -/
theorem result_unique_across_scopes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (collection : Bool)
    (w n z body out other : Fin m) (xs ys : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (Source.Formula.mem n w))
    (hxs : Derives Γ (SchemaIndexSyntax.chain n xs)) (hys : Derives Γ (SchemaIndexSyntax.chain n ys))
    (hx : Derives Γ (SchemaAxiomCompilation.schemaResult collection w n z body out xs))
    (hy : Derives Γ (SchemaAxiomCompilation.schemaResult collection w n z body other ys)) : Derives Γ (.equal out other) := by
  have he := scope_chain_unique hZ n ys xs hys hxs
  exact result_unique hZ collection w n z body out other xs hw hn hx (scopes_subst collection w n z body other ys xs he hy)

def uniqueResult {m} (collection : Bool) (w n z body out : Fin m) (scopes : Fin 4 → Fin m) : Source.Formula m := .all
  ((SchemaAxiomCompilation.schemaResult collection w.castSucc n.castSucc z.castSucc body.castSucc (Fin.last m) (fun i => (scopes i).castSucc)).imp
    (.equal (Fin.last m) out.castSucc))

def fiber {m} (collection : Bool) (w n z body : Fin m) (scopes : Fin 4 → Fin m) : Source.Formula m := .ex
  ((((Source.Formula.mem (Fin.last m) w.castSucc).conj
    (SchemaAxiomCompilation.schemaResult collection w.castSucc n.castSucc z.castSucc body.castSucc (Fin.last m) (fun i => (scopes i).castSucc))).conj
      (FormulaCodeSyntax.formulaCode w.castSucc (Fin.last m) z.castSucc z.castSucc)).conj
        (uniqueResult collection w.castSucc n.castSucc z.castSucc body.castSucc (Fin.last m) (fun i => (scopes i).castSucc)))

theorem uniqueResult_rename {m l} (collection : Bool) (w n z body out : Fin m) (scopes : Fin 4 → Fin m) (r : Fin m → Fin l) :
    (uniqueResult collection w n z body out scopes).rename r = uniqueResult collection (r w) (r n) (r z) (r body) (r out) (fun i => r (scopes i)) := by
  simp only [uniqueResult,Formula.rename,SchemaAxiomCompilation.schemaResult_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem fiber_rename {m l} (collection : Bool) (w n z body : Fin m) (scopes : Fin 4 → Fin m) (r : Fin m → Fin l) :
    (fiber collection w n z body scopes).rename r = fiber collection (r w) (r n) (r z) (r body) (fun i => r (scopes i)) := by
  simp only [fiber,Formula.rename,SchemaAxiomCompilation.schemaResult_rename,FormulaCodeSyntax.formulaCode_rename,
    uniqueResult_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

/-- Actual existence, complete closed type and ALL-candidate uniqueness from
one raw valid source body. No output, trace, maps or functional oracle. -/
theorem output_exists_typed_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (collection : Bool)
    (w n z body : Fin m) (scopes : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (Source.Formula.mem n w)) (hz : Derives Γ (empty z))
    (hc : Derives Γ (SchemaIndexSyntax.chain n scopes))
    (ha : Derives Γ (ProjectSourceCodeSyntax.sourceCode w body (sourceScope (SchemaAxiomCompilation.firstSite collection) scopes) z)) :
    Derives Γ (fiber collection w n z body scopes) := by
  let O := ((Source.Formula.mem (Fin.last m) w.castSucc).conj
    (SchemaAxiomCompilation.schemaResult collection w.castSucc n.castSucc z.castSucc body.castSucc (Fin.last m) (fun i => (scopes i).castSucc))).conj
      (FormulaCodeSyntax.formulaCode w.castSucc (Fin.last m) z.castSucc z.castSucc)
  let Δ := Context.add O (Context.image Formula.raise Γ)
  apply Derives.exE (p := O) (SchemaShellTyping.output_exists_typed hZ collection w n z body scopes hw hn hz hc ha)
  have hO : Derives Δ O := .hyp (Or.inl rfl)
  have hu : Derives Δ (uniqueResult collection w.castSucc n.castSucc z.castSucc body.castSucc (Fin.last m) (fun i => (scopes i).castSucc)) := by
    apply Derives.allI
    apply Derives.impI
    let Q := SchemaAxiomCompilation.schemaResult collection w.castSucc.castSucc n.castSucc.castSucc z.castSucc.castSucc body.castSucc.castSucc
      (Fin.last (m+1)) (fun i => (scopes i).castSucc.castSucc)
    let Ξ := Context.add Q (Context.image Formula.raise Δ)
    have hx2 : Derives Ξ (SchemaAxiomCompilation.schemaResult collection w.castSucc.castSucc n.castSucc.castSucc z.castSucc.castSucc body.castSucc.castSucc
        (Fin.last m).castSucc (fun i => (scopes i).castSucc.castSucc)) :=
      of_eq (SchemaAxiomCompilation.schemaResult_rename _ _ _ _ _ _ _ Fin.castSucc) (under (.conjR (.conjL hO)) Q)
    exact result_unique (ZFContext.under (ZFContext.under hZ O) Q) collection w.castSucc.castSucc n.castSucc.castSucc z.castSucc.castSucc body.castSucc.castSucc
      (Fin.last (m+1)) (Fin.last m).castSucc (fun i => (scopes i).castSucc.castSucc)
      (of_eq (by simp only [Formula.raise,omega_rename]) (under (under hw O) Q)) (under (under hn O) Q) (.hyp (Or.inl rfl)) hx2
  have hout : Derives Δ (fiber collection w.castSucc n.castSucc z.castSucc body.castSucc (fun i => (scopes i).castSucc)) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [O,Formula.instantiate,Formula.rename,SchemaAxiomCompilation.schemaResult_rename,
      FormulaCodeSyntax.formulaCode_rename,uniqueResult_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hO hu)
  exact of_eq (fiber_rename collection w n z body scopes Fin.castSucc).symm hout

def sentence {m} (collection : Bool) (w n z body : Fin m) (scopes : Fin 4 → Fin m) : Source.Sentence :=
  ((omega w).imp ((Source.Formula.mem n w).imp ((empty z).imp ((SchemaIndexSyntax.chain n scopes).imp
    ((ProjectSourceCodeSyntax.sourceCode w body (sourceScope (SchemaAxiomCompilation.firstSite collection) scopes) z).imp
      (fiber collection w n z body scopes)))))).close

theorem source_certificate {m} (collection : Bool) (w n z body : Fin m) (scopes : Fin 4 → Fin m) :
    Derives (Source.SetLanguage.ZF.at 0) (sentence collection w n z body scopes) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ := Context.add (ProjectSourceCodeSyntax.sourceCode w body (sourceScope (SchemaAxiomCompilation.firstSite collection) scopes) z)
    (Context.add (SchemaIndexSyntax.chain n scopes) (Context.add (empty z) (Context.add (Source.Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _) _
  exact output_exists_typed_unique hZ collection w n z body scopes (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem kernel_certificate {m} (collection : Bool) (w n z body : Fin m) (scopes : Fin 4 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence collection w n z body scopes)) :=
  ZFReplay.replay (TheoryTransport.sentence (source_certificate collection w n z body scopes))


/-- Native comparison gate also quantifies independent original scope witnesses. -/
def comparison_sentence {m} (collection : Bool) (w n z body out other : Fin m) (xs ys : Fin 4 → Fin m) : Source.Sentence :=
  ((omega w).imp ((Source.Formula.mem n w).imp ((SchemaIndexSyntax.chain n xs).imp ((SchemaIndexSyntax.chain n ys).imp
    ((SchemaAxiomCompilation.schemaResult collection w n z body out xs).imp
      ((SchemaAxiomCompilation.schemaResult collection w n z body other ys).imp (.equal out other))))))).close

theorem comparison_source_certificate {m} (collection : Bool) (w n z body out other : Fin m) (xs ys : Fin 4 → Fin m) :
    Derives (Source.SetLanguage.ZF.at 0) (comparison_sentence collection w n z body out other xs ys) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ := Context.add (SchemaAxiomCompilation.schemaResult collection w n z body other ys)
    (Context.add (SchemaAxiomCompilation.schemaResult collection w n z body out xs)
      (Context.add (SchemaIndexSyntax.chain n ys) (Context.add (SchemaIndexSyntax.chain n xs)
        (Context.add (Source.Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _) _) _
  exact result_unique_across_scopes hZ collection w n z body out other xs ys
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem comparison_kernel_certificate {m} (collection : Bool) (w n z body out other : Fin m) (xs ys : Fin 4 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (comparison_sentence collection w n z body out other xs ys)) :=
  ZFReplay.replay (TheoryTransport.sentence (comparison_source_certificate collection w n z body out other xs ys))

end PPAC.Migration.SchemaAxiomUnique
