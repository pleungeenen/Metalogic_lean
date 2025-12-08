
inductive PropForm where
  | tr     : PropForm
  | fls    : PropForm
  | var    : String → PropForm
  | conj   : PropForm → PropForm → PropForm
  | disj   : PropForm → PropForm → PropForm
  | impl   : PropForm → PropForm → PropForm
  | neg    : PropForm → PropForm
  | biImpl : PropForm → PropForm → PropForm
  deriving DecidableEq

open PropForm

def example1 := impl (conj (var "p") (var "q")) (var "r")


def List.unionStr (l1 l2 : List String) : List String :=
  l1 ++ (l2.filter (fun x => !l1.contains x))

namespace PropForm
declare_syntax_cat propform

syntax "prop!{" propform "}"  : term

syntax:max ident                        : propform
syntax "⊤"                              : propform
syntax "⊥"                              : propform
syntax:35 propform:36 " ∧ " propform:35 : propform
syntax:30 propform:31 " ∨ " propform:30 : propform
syntax:20 propform:21 " → " propform:20 : propform
syntax:20 propform:21 " ↔ " propform:20 : propform
syntax:max "¬ " propform:40             : propform
syntax:max "(" propform ")"             : propform

macro_rules
  | `(prop!{$p:ident}) => `(PropForm.var $(Lean.quote p.getId.toString))
  | `(prop!{⊤})        => `(ProfForm.tr)
  | `(prop!{⊥})        => `(ProfForm.fls)
  | `(prop!{¬ $p})     => `(PropForm.neg prop!{$p})
  | `(prop!{$p ∧ $q})  => `(PropForm.conj prop!{$p} prop!{$q})
  | `(prop!{$p ∨ $q})  => `(PropForm.disj prop!{$p} prop!{$q})
  | `(prop!{$p → $q})  => `(PropForm.impl prop!{$p} prop!{$q})
  | `(prop!{$p ↔ $q})  => `(PropForm.biImpl prop!{$p} prop!{$q})
  | `(prop!{($p:propform)}) => `(prop!{$p})



def complexity : PropForm → Nat
  | var _ => 0
  | tr => 0
  | fls => 0
  | neg A => complexity A + 1
  | conj A B => complexity A + complexity B + 1
  | disj A B => complexity A + complexity B + 1
  | impl A B => complexity A + complexity B + 1
  | biImpl A B => complexity A + complexity B + 1

def depth : PropForm → Nat
  | var _ => 0
  | tr => 0
  | fls => 0
  | neg A => depth A + 1
  | conj A B => Nat.max (depth A) (depth B) + 1
  | disj A B => Nat.max (depth A) (depth B) + 1
  | impl A B => Nat.max (depth A) (depth B) + 1
  | biImpl A B => Nat.max (depth A) (depth B) + 1

def vars : PropForm → List String
  | var s => [s]
  | tr => []
  | fls => []
  | neg A => vars A
  | conj A B => List.unionStr (vars A) (vars B)
  | disj A B => List.unionStr (vars A) (vars B)
  | impl A B => List.unionStr (vars A) (vars B)
  | biImpl A B => List.unionStr (vars A) (vars B)


def toString : PropForm → String
  | tr => "⊤"
  | fls => "⊥"
  | var s => s
  | neg A => "¬" ++ toString A
  | conj A B => "(" ++ toString A ++ " ∧ " ++ toString B ++ ")"
  | disj A B => "(" ++ toString A ++ " ∨ " ++ toString B ++ ")"
  | impl A B => "(" ++ toString A ++ " → " ++ toString B ++ ")"
  | biImpl A B => "(" ++ toString A ++ " ↔ " ++ toString B ++ ")"

instance : ToString PropForm where
  toString := PropForm.toString

end PropForm


def propExample := conj (var "p") (impl (var "q") (var "r"))
def propExample2 := prop!{p ∧ (q → r)}
#eval propExample2
#eval propExample2 = propExample
#eval propExample.toString

#eval propExample.complexity
#eval propExample.depth
#eval propExample.vars
#eval propExample.toString

def hello : String := "propositional logic"

/-test-/
def duality : PropForm -> PropForm
  | tr => fls
  | fls => tr
  | var s => var s
  | neg A => neg A
  | conj A B => disj A B
  | disj A B => conj A B
  | impl A B => impl A B
  | biImpl A B => biImpl A B

#eval duality (conj (var "p") (var "q"))
#eval duality (disj (var "k") (var "l"))
#eval duality (conj (conj (var "p") (var "q")) (var "r"))

def duality2 : PropForm -> PropForm
  | tr => tr
  | fls => fls
  | var s => var s
  | neg A => neg (duality2 A)
  | conj A B => disj (duality2 A) (duality2 B)
  | disj A B => conj (duality2 A) (duality2 B)
  | impl A B => conj (neg (duality2 A)) (duality2 B)
  | biImpl A B => disj (conj (neg (duality2 A)) (duality2 B)) (conj (neg (duality2 B)) (duality2 A))

  #eval duality2 (conj (conj (var "p") (var "k")) (var "l"))
  #eval duality2 (disj (disj (var "p") (var "k")) (var "l"))

/-moet negation pakken, dus fls => tr?-/
def auxiliary : PropForm -> PropForm
  | tr => fls
  | fls => tr
  | var s => neg (var s)
  | neg A => neg (auxiliary A)
  | conj A B => disj (auxiliary A) (auxiliary B)
  | disj A B => conj (auxiliary A) (auxiliary B)
  | impl A B => impl (auxiliary A) (auxiliary B)
  | biImpl A B => biImpl (auxiliary A) (auxiliary B)

/-PropForm1 = formule, String = variable, PropForm2 = vervanging en PropForm3 = resultaat-/
/-begrijp var hier niet vragen nog, zit ook error in-/
/-  | var A1, x, B => if x == A1 then B else var A1 was verkeerd, moest y zijn-/
def substitution (t : String) (D : PropForm) : PropForm → PropForm
  | tr => tr
  | fls => fls
  | var s => if s == t then D else var s
  | neg A => neg (substitution t D A)
  | conj A B => conj (substitution t D A) (substitution t D B)
  | disj A B => disj (substitution t D A) (substitution t D B)
  | impl A B => impl (substitution t D A) (substitution t D B)
  | biImpl A B=> biImpl (substitution t D A) (substitution t D B)

#eval substitution "p" (var "q") (var "p") == var "q"
#eval substitution "p" (var "q") tr == tr
#eval substitution "k" (var "l") (conj (var "k") (var "m")) == conj (var "l") (var "m")
