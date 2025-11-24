
inductive PropForm where
  | tr     : PropForm
  | fls    : PropForm
  | var    : String → PropForm
  | conj   : PropForm → PropForm → PropForm
  | disj   : PropForm → PropForm → PropForm
  | impl   : PropForm → PropForm → PropForm
  | neg    : PropForm → PropForm
  | biImpl : PropForm → PropForm → PropForm
  deriving Repr, DecidableEq

open PropForm

def example1 := impl (conj (var "p") (var "q")) (var "r")

def List.unionStr (l1 l2 : List String) : List String :=
  l1 ++ (l2.filter (fun x => !l1.contains x))

namespace PropForm

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

#eval propExample.complexity
#eval propExample.depth
#eval propExample.vars
#eval propExample.toString

def hello : String := "propositional logic"
