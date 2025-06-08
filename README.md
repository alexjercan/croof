# Croof Language Documentation

Croof is a minimal, readable proof-oriented language for defining and
evaluating mathematical objects and theorems. It enables formalization of
definitions, axioms, and algebraic manipulation through a simple and expressive
syntax.

---

## 📘 Table of Contents

1. [📚 Language Overview](#📚-language-overview)
2. [🔢 Types and Values](#🔢-types-and-values)
3. [✍️ Syntax](#✍️-syntax)
   - [Definitions (`def`)](#definitions-def)
   - [Universal Quantification (`forall`)](#universal-quantification-forall)
   - [Equations and Axioms](#equations-and-axioms)
   - [Evaluation (`eval`)](#evaluation-eval)
4. [🔧 Built-in Types and Operators](#🔧-built-in-types-and-operators)
5. [✍️ Writing Your Own Expressions](#✍️-writing-your-own-expressions)
6. [📝 Best Practices & Rules](#📝-best-practices--rules)
7. [📖 Examples](#📖-examples)
   - [Example 1: Hello World](#example-1-hello-world)
   - [Example 2: Natural Number Addition](#example-2-natural-number-addition)
8. [📦 Future Extensions](#📦-future-extensions)

---

## 📚 Language Overview

Croof is designed to:

- Define mathematical functions and properties
- Express universally quantified statements
- Evaluate expressions step by step using defined axioms
- Provide an intuitive syntax for writing mathematical rules

Croof operates similarly to a proof assistant, using rewrite rules and logical
identities to transform expressions.

---

## 🔢 Types and Values

Croof supports:

- **Natural Numbers** (`N`): values like `0`, `1`, `2`, etc., with successors using `succ(a)`
- **Booleans** (`Bool`): `"true"` and `"false"`

You can define your own types using `def`.

---

## ✍️ Syntax

### Definitions: `def`

Used to introduce new types or functions.

```croof
def <name> = <definition>               # Constant or type
def <name> : <T1> -> <T2> -> ... -> Tn  # Function type signature
```

Examples:

```croof
def + : N -> N -> N
def Bool = {"true", "false"}
```

### Universal Quantification: `forall`

Used to express statements that hold for all elements of a type.

```croof
forall <x> : <T> => <statement>
```

You can chain them:

```croof
forall x : N, forall y : N => <statement>
```

Example:

```croof
forall x : N => x + 0 = x
```

### Evaluation: `eval`

Used to evaluate expressions based on defined axioms and rules.

```croof
eval <expression>
```

Example:

```croof
eval 1 + 1
```

Outputs:

```text
Expression: 1 + 1
  - 1 + 1 => succ(0) + 1 (apply 1 = succ(0))
  - succ(0) + 1 => 0 + succ(1) (apply forall a : N, forall b : N => succ(a) + b = a + succ(b))
  - 0 + succ(1) => 0 + 2 (apply succ(1) = 2)
  - 0 + 2 => 2 (apply forall a : N => 0 + a = a)
Result: 2
```

## 🔧 Built-in Types and Operators

Croof includes several built-in types and operators:

- **Natural Numbers** (`ℕ`): Defined with `def N = {0, 1, 2, ...}`
- **Boolean Values**: Defined with `def Bool = {"true", "false"}`
- **Arithmetic Operators**: `+`, `*`, `-` (with axioms for natural numbers)
- **Logical Operators**: `&&`, `||` (for boolean values)
- **Comparison Operators**: `<` (for natural numbers)

## ✍️ Writing Your Own Expressions

You can create custom expressions using the defined syntax. For example, to
define a function that computes the successor of the successor of a natural
number, you can write:

```croof
def succ2 : N -> N
forall x : N => succ2(x) = succ(succ(x))
```

## 📝 Best Practices & Rules

- Use clear and descriptive names for definitions.
- Keep definitions simple and focused on a single concept.
- Use universal quantification to express general properties.
- Ensure that axioms are well-founded and logically sound.
- Test your definitions with `eval` to verify correctness.
- Document your definitions and axioms for clarity.
- Avoid circular definitions that can lead to infinite loops in evaluation.
- Use parentheses to clarify precedence in complex expressions.
- Follow a consistent naming convention for types and functions.

## 📖 Examples

### Example 1: Hello World

This example demonstrates a simple "Hello World" definition in Croof.

```croof
def Hello = {"Hello, World!"}

eval "Hello, World!"
```

### Example 2: Natural Number Addition

This example demonstrates how to define basic arithmetic operations on natural
numbers using Croof.

```croof
def + : N -> N -> N

forall a : N               => 0 + a = a
forall a : N, forall b : N => succ(a) + b = a + succ(b)

forall a : N, forall b : N => a + b = b + a
forall a : N, forall b : N, forall c : N => (a + b) + c = a + (b + c)

eval 1 + 1
```

Outputs:

```text
Expression: 1 + 1
  - 1 + 1 => succ(0) + 1 (apply 1 = succ(0))
  - succ(0) + 1 => 0 + succ(1) (apply forall a : N, forall b : N => succ(a) + b = a + succ(b))
  - 0 + succ(1) => 0 + 2 (apply succ(1) = 2)
  - 0 + 2 => 2 (apply forall a : N => 0 + a = a)
Result: 2
```

## 📦 Future Extensions

Future versions of Croof may include:
- Support for more complex data types (e.g., lists, tuples)
- Enhanced evaluation strategies (e.g., lazy evaluation)
- Improved error handling and debugging tools
- More built-in functions for common mathematical operations
