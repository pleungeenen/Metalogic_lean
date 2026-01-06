import MyLeanProject.Basic
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




@[simp]
theorem negation_evaluation (v : PropAssignment) (A : PropForm) :
  eval v (neg A) = !(eval v A) := by
  rfl

@[simp]
theorem conjunction_evaluation (v : PropAssignment) (A B : PropForm) :
  (eval v (conj A B)) = ((eval v A) && (eval v B)) := by
  rfl

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

/-llemma's-/

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
  (biImpl (conj A1 A2) (conj B1 B2)).eval v =
  ((biImpl A1 B1).eval v && (biImpl A2 B2).eval v) := by
  simp [PropForm.eval]
  sorry

lemma disjunction_congruence (A1 A2 B1 B2 : PropForm) (v : PropAssignment) :
  (biImpl A1 B1).eval v = (biImpl (disj A1 A2) (disj B1 B2)).eval v := by
  simp [PropForm.eval]
  sorry

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
  -- rw [negation_congruence A B]
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



/-cases checkt alle mogelijkheden, volgens tactics hfst in boek-/
/-<;> zorgt ervoor dat rfl op beide onderdelen wordt toegepast-/
/-simp[auxiliary, PropForm.eval] =  aan de linkerkant wordt de auxiliary geevalueerd, aan de rechterkant de negatie hiervan -/
/- rw = rewrite -/
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
/-bij var ook 2 cases?-/
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

/-de 2 var lemma's zeggen dat variabelen niet veranderen
bij toepassen van auxiliary of duality2-/
lemma auxiliary_variable (A : PropForm) : (auxiliary A).vars = A.vars := by
  sorry

lemma duality_variable (A : PropForm) : (duality2 A).vars = A.vars := by
  sorry

/-A <-> B dan ook auxiliary A <-> auxiliary B-/
lemma duality_biImpl (A B : PropForm) : (⊨ biImpl A B) -> (⊨biImpl (auxiliary A) (auxiliary B)) := by
  sorry


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

/-ik heb nog een andere substitution nodig denk ik? als ik het volgens het boek wil doen-/
/-twee cases, -> en <-?-/
theorem duality_theorem (A B : PropForm) : (⊨ (biImpl A B)) ↔ (⊨ (biImpl (duality2 A) (duality2 B))) := by
  constructor
  · intro h
    sorry
  · intro h
    sorry
