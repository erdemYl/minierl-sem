erlang_types
=====

An OTP library

Build
-----

    $ rebar3 compile

 
Open Questions
-----

* Are the subtype recursive calls improved by a tail-recursive variant?
  * e.g. `rec_fun() andalso rec_fun() andalso rec_fun()`
  * vs tail-recursive


Updates
-----

* **Maps -** starting point
  * **#{** key() => t() } ~ closed
  * **#{** key() => t(),  \_=>\_ **}** ~ open
  * keys can be *integers*, *atoms*, *tuples*
  * a map has always a **struct** part and a **dict** part
  * **struct** has forms **{** a := t1(), b := t2() **}**, open or closed, only singleton keys
  * **dict** has always the form **{** step() => t() **}**, open.

  
* **Maps -** representation
  * **#{** integer() => t1(), atom() => t2() **}** ~ **{** integer() => t1() **}** 
    ∧ **{** atom() => t2() **}** ∧ **{** tuple() => none() **}**
  * **#{** integer() => t(), \_=>\_ **}** ~ **{** integer() => t() **}**
    ∧ **{** atom() => any() **}** ∧ **{** tuple() => any() **}**
  * **#{** 1 := t1(), integer() => t2() **}**
    * ≠ **{** 1 := t1() **}** ∧ **{** integer() => t2() **}**
    * 1 has priority and is associated to t1()
    * currently not expressible in AST test
    * subtyping can handle this, though
  

* **Takeaway** 
  * intersection helps to build *closed* maps out of *open* dicts
  

* **Map Subtyping**
  * **phi** algorithm for *quasi K-step function* decomposition 
  * K = { integer(), atom(), tuple() }


* **Todo**
  * implement "**=>**" in structs (needed or could be bypassed?)
  * allow partitioning each step *(e.g. integer() ~ \*..4 ∨ 5..\*)*
    * partitions form a complete lattice
    * implement ∨, ∧ for partitions 
  * typing maps/constraint generation
  * type operator implementation *(selection, deletion, update)*

Roadmap
-----


* [x] V1 basic architecture
  * AST test spec defined
  * 1-functions, 2-tuples, intervals, atoms
  * generic bdd
  * hash-consing of types
  * subtyping
  * recursive types via type references

* [x] V2
  * tallying
   
* [ ] V3
  * types: n-tuples, n-functions
  * 
* [ ] V4
  * types: named, base, lists, bitstrings, records, specials, maps, ...

* [ ] V_opt1
  * lazy BDDs
  * hash-consing of `ty_rec` operations
  * hash-consing of BDD
  * hash-consing of BDD operations
