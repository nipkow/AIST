# PreStar

When analyzing context-free grammars, an interesting fact is the set of of predecessors of
any given string. Further, the set of predecessors of a set of strings `L`, `pre*(L)`, allows for
interesting applications. One first key result is the regularity: if `L` is regular, then so is
`pre*(L)`. Secondly, this method can be used to provide solutions to many different problems
regarding context-free grammars, such as the word-problem, emptiness problem, and more.

We formalize two algorithms to compute `pre*(L)` for a regular `L` (using NFAs as representation).
While the second algorithm is specifically tailored to grammars in extended-CNF, the former
is generally applicable. We design the formalization to be automatically executable,
allowing many different problems on context-free grammars to be solved automatically.
