import Lean

section utils
open Lean

/-- False Notation -/
notation "⊥" => False

/- plain numbers can't be used as identifiers so line number identifiers are prefixed with `L` -/
private abbrev mkLineId (n : Nat) : TSyntax [] := TSyntax.mk (mkIdent s!"L{n}")

/- theorem names are mildly obfuscated to avoid name clashes -/
private abbrev mkThmId (n : Name) : TSyntax [] := TSyntax.mk (mkIdent s!"T@{n}")

end utils

/-- Theorem Declaration

    Syntax: `thm <name> <vars> : <hyps> ⊢ <goal>`

    - `name` is the theorem name to be used in the `THM` proof command
    - `vars` is a space separated list of propositional variables
    - `hyps` is a comma separated list of hypotheses for the theorem
    - `goal` is the main theorem statement
-/
macro doc?:(docComment)? "thm " name:ident vars:ident* " : " hyps:term,* " ⊢ " goal:term " := " prf:term : command =>
  -- TODO: make docstrings work in a meaningful way
  -- TODO: can we get rid of the walrus?
  let ln := mkThmId name.getId
  `($[$doc?]? theorem $ln $[($vars : Prop)]* $[(_ : $hyps := by first | assumption | fail "missing hypothesis")]* : $goal := $prf)


/-- Basic Hilbert Proof Commands -/
declare_syntax_cat hbasic

/-- Proof Command

  Syntax: `proof <cmds> qed`

  - `cmds` is a sequence of proof commands on separate numbered lines

  Proof commands are of the shape `<lnum> <cmd> <args>` where `lnum` is the line number, `cmd` is the command name and `args` are the command arguments.
  Line numbers must be positive and increasing at each step.
  The last line of the proof should match the main statement of the theorem being proved.
-/
syntax "proof" (noWs "[" num "]")? withPosition(colGe hbasic)* "qed" : term

/- Syntax Checking -/
def checkCMD := Lean.Parser.checkLineEq "command (MP, DT, HYP, LEM)"
def checkTHM := Lean.Parser.checkLineEq "theorem name"
def checkARG := Lean.Parser.checkColGt "proposition"
def checkREF := Lean.Parser.checkLineEq "line number"
def checkVAR := Lean.Parser.checkLineEq "variable name"

/-- Modus Ponens 

  Syntax: `<lnum> MP <lref>`

  - `lnum` is the current line number
  - `lref` is a line reference for a conditional statement

  When the statement referred to by `lref` is `A → B` then this proof command searches for the hypothesis `A` among the previous lines.
  If `A` is found then it assigns `B` to the current line number.
-/
syntax num ws (checkCMD "MP ") (checkREF num) : hbasic

/-- Deduction Theorem 

  Syntax: `<lnum> DT`

  When the current goal is `A → B` then this proof command assigns `A` to the current line number and sets the goal to `B`. 
-/
syntax num ws (checkCMD "DT ") : hbasic

/-- Recall Hypothesis

  Syntax: `<lnum> HYP <prop>`

  - `lnum` is the current line number
  - `prop` is a propositional statement

  This proof command searches for `prop` among the theorem hypotheses and previous lines.
  If `prop` is found then it assigns `prop` to the current line number.
-/
syntax num ws (checkCMD "HYP ") (checkARG term:max) : hbasic

/-- Invoke Theorem 

  Syntax: `<lnum> THM <name> <args>`

  - `lnum` is the current line number
  - `name` is the name of the theorem invoked
  - `args` is a space separated list of propositions

  This proof command searches a theorem `name` declared using the `thm` command and then assigns `args` to the propositional variables of the theorem.
  If the theorem has hypotheses, it searches for each one among previous lines.
  Then it assigns the theorem's main proposition to the current line number.
-/
syntax num ws (checkCMD "THM ") (checkTHM ident) (colGt term:max)* : hbasic

/- TODO: document implementation -/
macro_rules
| `(proof qed) => `(by done)
| `(proof[$m] qed) => 
  let lm := mkLineId m.getNat
  `(by first | exact $lm | done)
| `(proof$[[$m]]? $n:num MP $ref $rest* qed) =>
  let m := match m with | some m => m.getNat | none => 0
  if m < n.getNat then 
    let ln := mkLineId n.getNat
    let lref := mkLineId ref.getNat
    `(have $ln : (_ : Prop) := $lref (by first | assumption | fail "missing hypothesis"); proof[$n] $rest* qed)
  else
    Lean.Macro.throwError "line numbers must be positive and increasing"
| `(proof$[[$m]]? $n:num DT $rest* qed) =>
  let m := match m with | some m => m.getNat | none => 0
  if m < n.getNat then 
    let ln := mkLineId n.getNat
    `(fun $ln : (_ : Prop) => proof[$n] $rest* qed)
  else
    Lean.Macro.throwError "line numbers must be positive and increasing"
| `(proof$[[$m]]? $n:num HYP $h $rest* qed) =>
  let m := match m with | some m => m.getNat | none => 0
  if m < n.getNat then 
    let ln := mkLineId n.getNat
    `(have $ln : ($h : Prop) := (by assumption); proof[$n] $rest* qed)
  else
    Lean.Macro.throwError "line numbers must be positive and increasing"
| `(proof$[[$m]]? $n:num THM $name:ident $args:term* $rest:hbasic* qed) =>
  let m := match m with | some m => m.getNat | none => 0
  if m < n.getNat then 
    let ln := mkLineId n.getNat
    let tn := mkThmId name.getId
    `(have $ln : (_ : Prop) := $tn $args*; proof[$n] $rest* qed)  
  else
    Lean.Macro.throwError "line numbers must be positive and increasing"

/- Basic Theorems

The two deduction rules Modus Ponens (`MP`) and Deduction Theorem (`DT`) only characterize implication.
The basic axioms below are necessary to define the other logical connectives:

- Negation (¬·)
- Conjunction (·∧·)
- Disjunction (·∨·)
- Biconditional (·↔·)

The proofs involve Lean core theorems since they can't be proved using only the basic rules of this system.

In addition to these basic axioms, the basic implication axioms S, K, I are defined.
This is because the DT is not actually necessary in the presence of these axioms, so we make them available to users who wish to avoid DT.

Also, Pierce's Law is presented as the only axiom from classical logic.
It is sufficient to derive all classical theorems and it has the advantage of being formulated only using implication.
Users that wish to work in intuitionistic logic should avoid this axiom.
The Lean `#print axioms` command is useful to determine whether Pierce's Law is used, even indirectly, in a proof.
-/
section basic_theorems

/-- Axiom I: a → a -/
thm AXI a : ⊢ a → a :=
proof
10 DT
qed

/-- Axiom K: a → b → a -/
thm AXK a b : ⊢ a → b → a :=
proof
10 DT
20 DT
30 HYP a
qed

/-- Axiom S: (a → b → c) → (a → b) → a → c -/
thm AXS a b c : ⊢ (a → b → c) → (a → b) → a → c :=
proof
10 DT
20 DT
30 DT
40 MP 20
50 MP 10
60 MP 50
qed

/-- Ex Falso Quodlibet: ⊥ → a -/
thm EXFALSO a :
⊢ ⊥ → a := False.elim

/-- Negation Introduction: (a → ⊥) → ¬ a -/
thm NOTI a :
⊢ (a → ⊥) → ¬ a := id

/-- Negation Elimination: ¬ a → a → ⊥ -/
thm NOTE a :
⊢ ¬ a → a → ⊥ := id

/-- Conjunction Introduction: a → b → a ∧ b -/
thm ANDI a b :
⊢ a → b → a ∧ b := And.intro

/-- Conjunction Elimination: (a → b → c) → a ∧ b → c -/
thm ANDE a b c :
⊢ (a → b → c) → a ∧ b → c := And.rec

/-- Conjunction Elimination (Left): a ∧ b → a -/
thm ANDL a b :
⊢ a ∧ b → a := -- And.left
proof
10 THM AXK a b
20 THM ANDE a b a
30 MP 20
qed

/-- Conjunction Elimination (Right): a ∧ b → b -/
thm ANDR a b :
⊢ a ∧ b → b := -- And.right
proof
10 THM AXK (b → b) a
20 THM AXI b
30 MP 10
40 THM ANDE a b b
50 MP 40
qed

/-- Disjunction Elimination: (a → c) → (b → c) → a ∨ b → c -/
thm ORE a b c :
⊢ (a → c) → (b → c) → a ∨ b → c := Or.rec

/-- Disjunction Introduction (Left): a → a ∨ b -/
thm ORL a b :
⊢ a → a ∨ b := Or.inl

/-- Disjunction Introduction (Right): b → a ∨ b -/
thm ORR a b :
⊢ b → a ∨ b := Or.inr

/-- Biconditional Introduction: (a → b) → (b → a) → (a ↔ b) -/
thm IFFI a b :
⊢ (a → b) → (b → a) → (a ↔ b) := Iff.intro

/-- Biconditional Elimination (Left): (a ↔ b) → a → b -/
thm IFFL a b :
⊢ (a ↔ b) → a → b := Iff.mp

/-- Biconditional Elimination (Right): (a ↔ b) → b → a -/
thm IFFR a b :
⊢ (a ↔ b) → b → a := Iff.mpr

/-- Pierce's Law: ((a → b) → a) → a -/
thm PIERCE a b : 
⊢ ((a → b) → a) → a :=
fun h => match Classical.em a with
| .inl ha => ha
| .inr na => h fun ha => absurd ha na

end basic_theorems

/- Testing Zone -/
section test_theorems

thm ANDIDEMR a :
⊢ a → a ∧ a :=
proof
10 DT
20 THM ANDI a a
30 MP 20
40 MP 30
qed

thm ANDIDEM a :
⊢ a ∧ a ↔ a :=
proof
10 THM ANDL a a
20 THM ANDIDEMR a
30 THM IFFI (a ∧ a) a
40 MP 30
50 MP 40
qed

thm ORIDEML a :
⊢ a ∨ a → a :=
proof
10 THM AXI a
20 THM ORE a a a
30 MP 20
40 MP 30
qed

thm ORIDEM :
⊢ a ∨ a ↔ a :=
proof
10 THM ORIDEML a
20 THM ORL a a
30 THM IFFI (a ∨ a) a
40 MP 30
50 MP 40
qed

end test_theorems
