# portfolio
in Portfolio/
- MiniLuaCompiler.lean: Dependently-typed AST compiler from a dependently typed syntax tree to Lua
- IntrinsicSTLC.lean: Lean4 interpretation of https://plfa.github.io/DeBruijn/
- WType.lean and RecursionSchemes.lean: Lean4 implementation of https://dl.acm.org/doi/pdf/10.1145/3563355; formalization of inductive types and recursion schemes and indexed recursion schemes on them
- RecursorTheoremsAndManualCompilation.lean: Theorems about inductive type recursors and manual compilation of nested inductive type eliminator.
- WriterMonadMacro.lean: Lean4 metaprogramming; macro that transforms a monadic value into a WriterT type value with logging, automatically

