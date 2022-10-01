import Lean

section utils
open Lean

/-- True Notation -/
notation "⊤" => True

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
abbrev checkCMD := Lean.Parser.checkLineEq "command (MP, DT, HYP, LEM)"
abbrev checkTHM := Lean.Parser.checkLineEq "theorem name"
abbrev checkARG := Lean.Parser.checkColGt "proposition"
abbrev checkREF := Lean.Parser.checkLineEq "line number"

open Lean.Parser (semicolonOrLinebreak)

/-- Modus Ponens 

  Syntax: `<lnum> MP <lref>`

  - `lnum` is the current line number
  - `lref` is a line reference for a conditional statement

  When the statement referred to by `lref` is `A → B` then this proof command searches for the hypothesis `A` among the previous lines.
  If `A` is found then it assigns `B` to the current line number.
-/
syntax num ws (checkCMD "MP ") (checkREF num) semicolonOrLinebreak : hbasic

/-- Deduction Theorem 

  Syntax: `<lnum> DT`

  When the current goal is `A → B` then this proof command assigns `A` to the current line number and sets the goal to `B`. 
-/
syntax num ws (checkCMD "DT ") semicolonOrLinebreak : hbasic

/-- Recall Hypothesis

  Syntax: `<lnum> HYP <prop>`

  - `lnum` is the current line number
  - `prop` is a propositional statement

  This proof command searches for `prop` among the theorem hypotheses and previous lines.
  If `prop` is found then it assigns `prop` to the current line number.
-/
syntax num ws (checkCMD "HYP ") (checkARG term:max) semicolonOrLinebreak : hbasic

/-- Invoke Theorem 

  Syntax: `<lnum> THM <name> <args>`

  - `lnum` is the current line number
  - `name` is the name of the theorem invoked
  - `args` is a space separated list of propositions

  This proof command searches a theorem `name` declared using the `thm` command and then assigns `args` to the propositional variables of the theorem.
  If the theorem has hypotheses, it searches for each one among previous lines.
  Then it assigns the theorem's main proposition to the current line number.
-/
syntax num ws (checkCMD "THM ") (checkTHM ident) (colGt term:max)* semicolonOrLinebreak : hbasic

/- TODO: document implementation -/
open Lean in macro_rules
| `(proof qed%$tk) => withRef tk `(by done)
| `(proof[$m] qed%$tk) => 
  let lm := mkLineId m.getNat
  withRef tk `(by first | exact $lm | done)
| `(proof$[[$m]]? $n:num MP%$tk $ref; $rest* qed) =>
  let m := match m with | some m => m.getNat | none => 0
  if m < n.getNat then 
    let ln := mkLineId n.getNat
    let lref := mkLineId ref.getNat
    withRef n `(have $ln : (_ : Prop) := $lref (by first | assumption | fail "missing hypothesis"); proof[$n] $rest* qed)
  else
    Macro.throwErrorAt n "line numbers must be positive and increasing"
| `(proof$[[$m]]? $n:num DT%$tk; $rest* qed) =>
  let m := match m with | some m => m.getNat | none => 0
  if m < n.getNat then 
    let ln := mkLineId n.getNat
    withRef n `(fun $ln : (_ : Prop) => proof[$n] $rest* qed)
  else
    Macro.throwErrorAt n "line numbers must be positive and increasing"
| `(proof$[[$m]]? $n:num HYP%$tk $h; $rest* qed) =>
  let m := match m with | some m => m.getNat | none => 0
  if m < n.getNat then 
    let ln := mkLineId n.getNat
    withRef n `(have $ln : ($h : Prop) := (by assumption); proof[$n] $rest* qed)
  else
    Macro.throwErrorAt n "line numbers must be positive and increasing"
| `(proof$[[$m]]? $n:num THM%$tk $name:ident $args:term*; $rest* qed) =>
  let m := match m with | some m => m.getNat | none => 0
  if m < n.getNat then 
    let ln := mkLineId n.getNat
    let tn := mkThmId name.getId
    withRef n `(have $ln : (_ : Prop) := $tn $args*; proof[$n] $rest* qed)  
  else
    Macro.throwErrorAt n "line numbers must be positive and increasing"

/- Basic Theorems

The two deduction rules Modus Ponens (`MP`) and Deduction Theorem (`DT`) only characterize implication.
The basic axioms below are necessary to define the other logical connectives:

- True (⊤)
- False (⊥)
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

/-- Trivial: ⊤ -/
thm TRIV : 
⊢ ⊤ := True.intro

/-- True Elimination: (⊤ → a) → a -/
thm THUS a :
⊢ (⊤ → a) → a :=
proof
10 DT
20 THM TRIV;
30 MP 10
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

thm IFTRANS a b c :
⊢ (a → b) → (b → c) → a → c :=
proof
10 DT
20 DT
30 DT
40 MP 10
50 MP 20
qed

thm IFLCOMM a b c :
⊢ (a → b → c) → b → a → c :=
proof
10 DT
20 DT
30 DT
40 MP 10
50 MP 40
qed

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

thm ANDCOMM a b :
⊢ a ∧ b → b ∧ a :=
proof
10 THM ANDE a b (b ∧ a)
20 THM IFLCOMM b a (b ∧ a)
30 THM ANDI b a
40 MP 20
50 MP 10
qed

thm ANDASSOCL a b c :
⊢ a ∧ (b ∧ c) → (a ∧ b) ∧ c :=
proof
10 DT
20 THM ANDL a (b ∧ c)
30 MP 20
40 THM ANDR a (b ∧ c)
50 MP 40
60 THM ANDL b c
70 MP 60
80 THM ANDR b c
90 MP 80
100 THM ANDI a b
110 MP 100
120 MP 110
130 THM ANDI (a ∧ b) c
140 MP 130
150 MP 140
qed

thm ANDASSOCR a b c :
⊢ (a ∧ b) ∧ c → a ∧ (b ∧ c) :=
proof
10 DT
20 THM ANDR (a ∧ b) c
30 MP 20
40 THM ANDL (a ∧ b) c
50 MP 40
60 THM ANDR a b
70 MP 60
80 THM ANDL a b
90 MP 80
100 THM ANDI b c
110 MP 100
120 MP 110
130 THM ANDI a (b ∧ c)
140 MP 130
150 MP 140
qed

thm ANDASSOC a b c :
⊢ (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) :=
proof
10 THM ANDASSOCL a b c
20 THM ANDASSOCR a b c
30 THM IFFI ((a ∧ b) ∧ c) (a ∧ (b ∧ c))
40 MP 30
50 MP 40
qed

thm ANDTRUEL a :
⊢ ⊤ ∧ a ↔ a :=
proof
10 THM TRIV;
20 THM ANDR ⊤ a
30 THM ANDI ⊤ a
40 MP 30
50 THM IFFI (⊤ ∧ a) a
60 MP 50
70 MP 60 
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

thm ORCOMM a b :
⊢ a ∨ b → b ∨ a :=
proof
10 THM ORL b a
20 THM ORR b a
30 THM ORE a b (b ∨ a)
40 MP 30
50 MP 40
qed

thm ORASSOCL a b c :
⊢ a ∨ (b ∨ c) → (a ∨ b) ∨ c :=
proof
10 DT
20 THM ORE a (b ∨ c) ((a ∨ b) ∨ c)
30 THM ORL a b
40 THM ORL (a ∨ b) c
50 THM IFTRANS a (a ∨ b) ((a ∨ b) ∨ c)
60 MP 50
70 MP 60
80 MP 20
90 THM ORE b c ((a ∨ b) ∨ c)
100 THM ORR a b
110 THM ORL (a ∨ b) c
120 THM ORR (a ∨ b) c
130 THM IFTRANS b (a ∨ b) ((a ∨ b) ∨ c)
140 MP 130
150 MP 140
160 MP 90
170 MP 160
180 MP 80
190 MP 180
qed

thm ORASSOCR a b c :
⊢ (a ∨ b) ∨ c → a ∨ (b ∨ c) :=
proof
10 DT
20 THM ORE a b (a ∨ (b ∨ c))
30 THM ORL a (b ∨ c)
40 THM ORL b c
50 THM ORR a (b ∨ c)
60 THM IFTRANS b (b ∨ c) (a ∨ (b ∨ c))
70 MP 60
80 MP 70
90 MP 20
100 MP 90
110 THM ORR b c
120 THM IFTRANS c (b ∨ c) (a ∨ (b ∨ c))
130 MP 120
140 MP 130
150 THM ORE (a ∨ b) c (a ∨ (b ∨ c))
160 MP 150
170 MP 160
180 MP 170
qed

thm ORASSOC a b c :
⊢ (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) :=
proof
10 THM ORASSOCL a b c
20 THM ORASSOCR a b c
30 THM IFFI ((a ∨ b) ∨ c) (a ∨ (b ∨ c))
40 MP 30
50 MP 40
qed

thm ORRESL a b :
⊢ a ∨ b → ¬a → b :=
proof
10 DT
20 DT
30 THM ORE a b b
40 THM IFTRANS a ⊥ b
50 THM NOTE a
60 MP 50
70 MP 40
80 THM EXFALSO b
90 MP 70
100 MP 30
110 THM AXI b
120 MP 100
130 MP 120
qed

thm ORRESR a b :
⊢ a ∨ b → ¬b → a :=
proof
10 DT
20 DT
30 THM ORE a b a
40 THM AXI a
50 MP 30
60 THM IFTRANS b ⊥ a
70 THM NOTE b
80 MP 70
90 MP 60
100 THM EXFALSO a
110 MP 90
120 MP 50
130 MP 120
qed

thm ANDDISTRIBL a b c :
⊢ a ∧ (b ∨ c) → (a ∧ b) ∨ (a ∧ c) :=
proof
10 DT
20 THM ANDL a (b ∨ c)
30 MP 20
40 THM ANDR a (b ∨ c)
50 MP 40
60 THM ORE b c ((a ∧ b) ∨ (a ∧ c))
70 THM IFTRANS b (a ∧ b) ((a ∧ b) ∨ (a ∧ c))
80 THM ANDI a b
90 MP 80
100 MP 70
110 THM ORL (a ∧ b) (a ∧ c)
120 MP 100
130 THM IFTRANS c (a ∧ c) ((a ∧ b) ∨ (a ∧ c))
140 THM ANDI a c
150 MP 140
160 MP 130
170 THM ORR (a ∧ b) (a ∧ c)
180 MP 160
190 MP 60
200 MP 190
210 MP 200
qed

end test_theorems
