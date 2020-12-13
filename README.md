# Automated Temporal Verification for Hiphop.js
## Towards a Mixed Synchronous and Asynchronous Concurrency

HipHop.js is a reactive language that integrates Esterel’s synchronous concurrency and preemption with JavaScript’s asynchrony. Existing temporal verification techniques haven’t been able to tackle such a blending of both concurrency mod- els in the context of a mainstream web-oriented language. We propose a solution via a Hoare-style forward verifier and a term rewriting system (T.r.s) on Dependent Effects. The first contribution is the effects logic captures disjunctive value-dependent traces including possible infinite sequences. As a second contribution, by avoiding the complex translation into automata, our purely algebraic T.r.s efficiently checks the language inclusions among expressive (beyond context-free) Dependent Effects. To demonstrate our method’s feasibil- ity, we prototype this logic; prove its soundness; provide experimental results and a number of case studies.

### To Compile:

```
git clone https://github.com/songyahui/VerifySyncAsync.git
cd SyncedEffects
chmod 755 clean 
chmod 755 compile 
./compile
```

### Dependencies:

```
opam switch create 4.07.1
eval $(opam env)
sudo apt-get install menhir
sudo apt-get install z3
```

{A, B , C} /\ {B, C} |- {A}

{A} |- {A, B , C} /\ {B, C}
{A} |- {B} -> false

emp |- 
-------------------------------------------
{A}  |- {A} || O  and O  |- {A} || O
-----------------------------
{A} || O  |- {A} || O  true  
