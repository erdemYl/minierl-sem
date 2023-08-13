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


Roadmap
-----


V 1 Basic
===========

* [x] v1 basic architecture
  * AST test spec defined
  * arrows, 2-tuples, intervals, atoms
  * generic bdd
  * hash-consing of types
  * subtyping
  * recursive types via type references

* [ ] V2
  * tallying

* [ ] V3
  * lazy BDDs
  * hash-consing of ty_rec operations
  * hash-consing of BDD
  * hash-consing of BDD operations

* [ ] V4 
  * types: base
  * 
* [ ] V5 
  * types: n-tuples, n-functions
  * 
* [ ] V6 
  * types: lists, bitstrings, records, specials, ...
