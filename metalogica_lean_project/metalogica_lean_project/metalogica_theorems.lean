import metalogica_lean_project.metalogica_functions
import Mathlib.Tactic


open PropForm

def PropAssignment := List (String × Bool)

namespace PropAssignment

def eval (v : PropAssignment) (s : String) : Bool :=
  match v.find? (fun p => p.1 == s) with
  | some (_, b) => b
  | none => false


def mk (l : List (String × Bool)) : PropAssignment := l

end PropAssignment

def PropForm.eval (v : PropAssignment) : PropForm → Bool
  | var s => v.eval s
  | tr => true
  | fls => false
  | neg A => !(eval v A)
  | conj A B => (eval v A) && (eval v B)
  | disj A B => (eval v A) || (eval v B)
  | impl A B => !(eval v A) || (eval v B)
  | biImpl A B => (!(eval v A) || (eval v B)) && (!(eval v B) || (eval v A))


def example2 := biImpl (disj (var "p") (var "k")) (var "r")
#eval example2


def allSublists : List α → List (List α)
  | [] => [[]]
  | (a :: as) =>
      let recval := allSublists as
      recval.map (a :: ·) ++ recval

def truthTable (A : PropForm) : List (List Bool × Bool) :=
  let vars := A.vars
  let assignments := (allSublists vars).map (fun l => PropAssignment.mk (l.map (·, true)))
  let evalLine := fun v : PropAssignment => (vars.map v.eval, A.eval v)
  assignments.map evalLine


def PropForm.isValid (A : PropForm) : Bool :=
  List.all (truthTable A) Prod.snd

def PropForm.isSat (A : PropForm) : Bool :=
  List.any (truthTable A) Prod.snd

notation "⊨" A => PropForm.isValid A
#check ⊨ var "p"

notation A "AND" B => PropForm.conj A B
#eval var "p" AND var "q"

notation A "OR" B => PropForm.disj A B
#eval var "p" OR var "q"


/-@[simp] + lemma's:-/
@[simp]
theorem negation_evaluation (v : PropAssignment) (A : PropForm) :
  eval v (neg A) = !(eval v A) := by
  rfl

@[simp]
theorem conjunction_evaluation (v : PropAssignment) (A B : PropForm) :
  (eval v (conj A B)) = ((eval v A) && (eval v B)) := by
  rfl

lemma reflexive_biImpl (A : PropForm) : ⊨ biImpl A A := by
 simp [PropForm.isValid]
 intro a
 by_contra h
 simp [truthTable, PropForm.eval] at h

lemma negation_congruence (A B : PropForm) (v : PropAssignment) :
    (biImpl A B).eval v = (biImpl (neg A) (neg B)).eval v := by
      simp [PropForm.eval]
      grind

lemma conjunction_congruence (A1 A2 B1 B2 : PropForm) (v : PropAssignment) :
  ((biImpl A1 B1).eval v && (biImpl A2 B2).eval v) = true → (biImpl (conj A1 A2) (conj B1 B2)).eval v = true:= by
  simp [PropForm.eval]
  grind

lemma disjunction_congruence (A1 A2 B1 B2 : PropForm) (v : PropAssignment) :
  ((biImpl A1 B1).eval v && (biImpl A2 B2).eval v) = true → (biImpl (disj A1 A2) (disj B1 B2)).eval v = true:= by
  simp [PropForm.eval]
  grind

lemma implication_congruence (A1 A2 B1 B2 : PropForm) (v : PropAssignment) :
  (biImpl A1 B1).eval v = (biImpl (impl A1 A2) (impl B1 B2)).eval v := by
  simp [PropForm.eval]
  sorry

lemma biimplication_congruence (A1 A2 B1 B2 : PropForm) (v : PropAssignment) :
  (biImpl A1 B1).eval v = (biImpl (biImpl A1 A2) (biImpl B1 B2)).eval v := by
  simp [PropForm.eval]
  sorry


 lemma negation_biImpl (A B : PropForm) (h : ⊨ biImpl A B) :
    (⊨ biImpl (neg A) (neg B)) := by
  simp [PropForm.isValid]
  simp [PropForm.isValid] at h
  intro a
  specialize h a
  simp [truthTable] at h
  simp [truthTable]
  intro x g
  specialize h x
  intro j
  simp[PropAssignment.mk] at h
  simp[PropAssignment.mk]
  have auxiliary : List.map (PropAssignment.eval (List.map (fun x => (x, true)) x)) (A.biImpl B).vars = a →
    eval (List.map (fun x => (x, true)) x) (A.biImpl B) = true := by
      apply h g
  rw[←negation_congruence]
  apply auxiliary j

lemma conjunction_biImpl (A1 A2 B1 B2 : PropForm) (h1 : ⊨ biImpl A1 B1) (h2 : ⊨ biImpl A2 B2) :
  ⊨ biImpl (conj A1 A2) (conj B1 B2) := by
  simp [PropForm.isValid, truthTable]
  intro a
  let v := PropAssignment.mk (a.map (fun x => (x, true)))
  have eval1 : (A1.biImpl B1).eval v = true := by
    sorry
  have eval2 : (A2.biImpl B2).eval v = true := by
    sorry
  simp [PropForm.eval]
  sorry

lemma disjunction_biImpl (A1 A2 B1 B2 : PropForm)
  (h1 : ⊨ biImpl A1 B1) (h2 : ⊨ biImpl A2 B2) :
  ⊨ biImpl (disj A1 A2) (disj B1 B2) := by
  sorry

lemma implication_biImpl (A1 A2 B1 B2 : PropForm)
  (h1 : ⊨ biImpl A1 B1) (h2 : ⊨ biImpl A2 B2) :
  ⊨ biImpl (impl A1 A2) (impl B1 B2) := by
  sorry

lemma biimplication_biImpl (A1 A2 B1 B2 : PropForm)
  (h1 : ⊨ biImpl A1 B1) (h2 : ⊨ biImpl A2 B2) :
  ⊨ biImpl (biImpl A1 A2) (biImpl B1 B2) := by
  sorry

def testAssignment := PropAssignment.mk [("p", true), ("q", true), ("r", true)]

#eval propExample.eval testAssignment
#eval allSublists propExample.vars
#eval truthTable propExample
#eval propExample.isValid
#eval propExample.isSat



/- rw = rewrite -/
/-2.3.11-/
theorem auxiliary_theorem (A : PropForm) (v : PropAssignment) : (auxiliary A).eval v = (neg A).eval v := by
  induction A with
    | tr
    | fls
    | var s =>
      simp[auxiliary, PropForm.eval]
    | neg A ih =>
      simp[auxiliary, PropForm.eval]
      rw[ih]
      simp
    | conj A1 A2 ih1 ih2 =>
      simp[auxiliary, PropForm.eval]
      rw[ih1, ih2]
      simp
    | disj A1 A2 ih1 ih2 =>
      simp[auxiliary, PropForm.eval]
      rw[ih1, ih2]
      simp
    | impl A1 A2 ih1 ih2 =>
      simp[auxiliary, PropForm.eval]
      rw[ih1, ih2]
      simp
    | biImpl A1 A2 ih1 ih2 =>
      simp[auxiliary, PropForm.eval]
      rw[ih1, ih2]
      simp



/-intro is introduceren van iets nieuws.-/
/-bij var ook 2 cases-/
/-exact bewijs het voor de goal-/
theorem substitution_theorem (A B C : PropForm) (t : String) :
(⊨ (biImpl A B)) -> (⊨ (biImpl (substitution t A C) (substitution t B C))) := by
intro h
induction C with
 | tr =>
    simp[substitution]
    apply reflexive_biImpl tr
 | fls =>
   simp[substitution]
   apply reflexive_biImpl fls
 | var s =>
   by_cases g : s = t
   · simp[substitution]
     simp[g]
     exact h
   · simp[substitution]
     simp[g]
     apply reflexive_biImpl (var s)
 | neg A ih =>
   simp[substitution]
   apply negation_biImpl
   exact ih
 | conj A1 A2 ih1 ih2 =>
   simp[substitution]
   apply conjunction_biImpl
   exact ih1
   exact ih2
 | disj A1 A2 ih1 ih2 =>
   simp[substitution]
   apply disjunction_biImpl
   exact ih1
   exact ih2
 | impl A1 A2 ih1 ih2 =>
   simp[substitution]
   apply implication_biImpl
   exact ih1
   exact ih2
 | biImpl A1 A2 ih1 ih2 =>
   simp[substitution]
   apply biimplication_biImpl
   exact ih1
   exact ih2

/-@[simp] + lemma's-/
/-A <-> B dan ook auxiliary A <-> auxiliary B-/
lemma auxiliary_biImpl (A B : PropForm) : (⊨ biImpl A B) -> (⊨biImpl (auxiliary A) (auxiliary B)) := by
  sorry

/-auxiliary verandert true in false en andersom-/
@[simp]
lemma aux_tr : auxiliary tr = fls := rfl

@[simp]
lemma aux_fls : auxiliary fls = tr := rfl

@[simp]
lemma vars_biImpl (A B : PropForm) : (biImpl A B).vars = A.vars ∪ B.vars := by
sorry

@[simp]
lemma vars_conj (A B : PropForm) : (conj A B).vars = A.vars ∪ B.vars := by
sorry

/-ze zeggen allemaal dat de variabelen hetzelfde blijven bij omzetting-/
@[simp]
lemma vars_negation (A : PropForm) : (neg A).vars = A.vars := rfl

@[simp]
lemma vars_auxiliary (A : PropForm) : (auxiliary A).vars = A.vars := by
  sorry

@[simp]
lemma vars_duality2 (A : PropForm) : (duality2 A).vars = A.vars := by
  sorry

/-φ∗ = φd [¬p0, . . . , ¬pn/p0, . . . , pn]-/
lemma auxiliary_lemma (A : PropForm) :
    auxiliary A = simultaneous_substitution (A.vars.map (fun s => (s, neg (var s)))) (duality2 A) := by
    sorry

/-2.3.12 moet opnieuw, niet met gewone auxiliary vanwege ⊨ teken-/
lemma auxiliary2 (A : PropForm) : ⊨ biImpl (auxiliary A) (neg A) := by
sorry

/-theorem van simultaneous substitution-/
theorem simultaneous_substitution_theorem (A B : PropForm) (s : List (String × PropForm)) :
  (⊨ biImpl A B) → (⊨ biImpl (simultaneous_substitution s A) (simultaneous_substitution s B)) := by
  sorry

/-φ∗[¬p0,...,¬pn/p0,...,pn] = φd[¬¬p0,...,¬¬pn/p0,...,pn] uit van dalen boek-/
@[simp]
lemma auxiliary_dualitynegation (A : PropForm) : simultaneous_substitution (A.vars.map (fun s => (s, neg (var s)))) (auxiliary A) =
    simultaneous_substitution (A.vars.map (fun s => (s, neg (neg (var s))))) (duality2 A) := by
  sorry


/-By the Substitution Theorem |  φd ↔ φ∗[¬p0, . . . , ¬pn/p0, . . . , pn].-/
lemma substitution_duality_lemma (A : PropForm) :
    ⊨ biImpl (duality2 A) (simultaneous_substitution (A.vars.map (fun s => (s, neg (var s)))) (auxiliary A)) := by
      have step_1 : ⊨ biImpl (duality2 A) (simultaneous_substitution (A.vars.map (fun s => (s, neg (neg (var s))))) (duality2 A)) := by
        sorry
      simp
      grind

/-2 x duality toepassen = origineel-/
lemma duality_involutory (A : PropForm) (v : PropAssignment) :
    (duality2 (duality2 A)).eval v = A.eval v := by
  induction A with
  | tr => rfl
  | fls => rfl
  | var s => rfl
  | neg A ih => simp [duality2, ih]
  | conj A1 A2 ih1 ih2 => simp [duality2, ih1, ih2]
  | disj A1 A2 ih1 ih2 => simp [duality2, PropForm.eval, ih1, ih2]
  | impl A1 A2 ih1 ih2 => simp [duality2, PropForm.eval, ih1, ih2]
  | biImpl A1 A2 ih1 ih2 => simp [duality2, PropForm.eval, ih1, ih2]

/-lemma's voor duality:-/
/-als A<-> B en B<-> C dan A<->C-/
lemma biImpl_connection (A B C : PropForm) :
    (⊨ biImpl A B) → (⊨ biImpl B C) → (⊨ biImpl A C) := by
  sorry
/-als A<->B dan B<->A-/
lemma biImpl_symmetry (A B : PropForm) :
    (⊨ biImpl A B) → (⊨ biImpl B A) := by
  sorry
/-duality_involutory als met ⊨ teken-/
lemma duality_involutory_valid (A : PropForm) :
    ⊨ biImpl (duality2 (duality2 A)) A := by
  sorry

lemma auxiliary_to_duality (A B : PropForm) :
    (⊨ biImpl (auxiliary A) (auxiliary B)) → (⊨ biImpl (duality2 A) (duality2 B)) := by
    intro h
    /-φ∗ = φd [¬p0, . . . , ¬pn/p0, . . . , pn] de eerste 2 stappen is de regel voor beide formules-/
    have step1 : auxiliary A = simultaneous_substitution (A.vars.map (fun s => (s, neg (var s)))) (duality2 A) :=
    auxiliary_lemma A
    have step2 : auxiliary B = simultaneous_substitution (B.vars.map (fun s => (s, neg (var s)))) (duality2 B) :=
    auxiliary_lemma B
    /- /-By the Substitution Theorem |  φd ↔ φ∗[¬p0, . . . , ¬pn/p0, . . . , pn].-/ -/
    have step3 : ⊨ biImpl (duality2 A) (simultaneous_substitution (A.vars.map (fun s => (s, neg (var s)))) (auxiliary A)) :=
    substitution_duality_lemma A
    have step4 : ⊨ biImpl (duality2 B) (simultaneous_substitution (B.vars.map (fun s => (s, neg (var s)))) (auxiliary B)) :=
    substitution_duality_lemma B
    sorry


lemma duality_biImpl (A B : PropForm) : (⊨ biImpl A B) → (⊨ biImpl (duality2 A) (duality2 B)) := by
  intro h
  /-Since φ ↔ ψ, also  ¬φ ↔ ¬ψ-/
  have step1 : ⊨ biImpl (neg A) (neg B) := negation_biImpl A B h
  /- By Corollary 2.3.12 φ∗ ↔ ¬φ, ψ∗ ↔ ¬ψ-/
  have step2 : ⊨ biImpl (auxiliary A) (neg A) := auxiliary2 A
  have step3 : ⊨ biImpl (auxiliary B) (neg B) := auxiliary2 B
  /-Hence φ∗ ↔ ψ∗ in de volgende stappen:
     met biimpl_symmetry kunnen we van negatieB <-> auxiliaryB-/
  have step4 : ⊨ biImpl (neg B) (auxiliary B) := biImpl_symmetry (auxiliary B) (neg B) step3
  /- willen dat negatie A <-> auxiliary B,
      negatie A <-> negatie B, negatie B <-> auxiliary B, met transitiviteit van negatie A <-> auxiliary B-/
  have step5 : ⊨ biImpl (neg A) (auxiliary B) := biImpl_connection (neg A) (neg B) (auxiliary B) step1 step4
  /- auxiliary A <-> negatie A, negatie A <-> auxiliary B, met transitiviteit auxiliary A <-> auxiliary B -/
  have step6 : ⊨ biImpl (auxiliary A) (auxiliary B) := biImpl_connection (auxiliary A) (neg A) (auxiliary B) step2 step5
  /- dit gaat van auxiliary A <-> auxiliary B naar duality A <-> duality B-/
  exact auxiliary_to_duality A B step6

/- omgekeerde richting, als dualityA <-> dualityB dan A <->B-/
lemma duality_biImpl_reversed (A B : PropForm) : (⊨ biImpl (duality2 A) (duality2 B)) → (⊨ biImpl A B) := by
  intro h
  /- als dualityA <-> dualityB dan met duality2_biimpl duality duality A <-> duality duality B-/
  have step1 : ⊨ biImpl (duality2 (duality2 A)) (duality2 (duality2 B)) := duality_biImpl (duality2 A) (duality2 B) h
  /- duality 2 keer toepassen geeft de originele formule terug, dualitydualityA <-> A-/
  have step2 : ⊨ biImpl (duality2 (duality2 A)) A := duality_involutory_valid A
  have step3 : ⊨ biImpl (duality2 (duality2 B)) B := duality_involutory_valid B
  /- A <-> dualitydualityA-/
  have step4 : ⊨ biImpl A (duality2 (duality2 A)) := biImpl_symmetry (duality2 (duality2 A)) A step2
  /- A <-> dualitydualityA en dualitydualityA <-> dualitydualityB, wordt A <->dualitydualityB-/
  have step5 : ⊨ biImpl A (duality2 (duality2 B)) := biImpl_connection A (duality2 (duality2 A)) (duality2 (duality2 B)) step4 step1
  /- A <-> dualitydualityB met dualitydualityB <-> B wordt A <-> B-/
  exact biImpl_connection A (duality2 (duality2 B)) B step5 step3


/-twee cases, -> en <--/
theorem duality_theorem (A B : PropForm) : (⊨ (biImpl A B)) ↔ (⊨ (biImpl (duality2 A) (duality2 B))) := by
  constructor
  · intro h
    exact duality_biImpl A B h
  · intro h
    exact duality_biImpl_reversed A B h


/-extra-/
theorem modus_ponens (A B : PropForm) (h1 : ⊨ impl A B) (h1 : ⊨ A) : ⊨ B := by
  sorry


theorem term (p q : Prop) (h1 : p) (h2 : q) : p ∧ q :=
  ⟨h1, h2⟩


theorem tactic (p q : Prop) (h1 : p) (h2 : q) : p ∧ q := by
  constructor
  apply h1
  apply h2
