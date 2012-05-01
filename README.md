
ZML README
==========

ZML is a work-in-progress ML compiler which targets the Z-Machine (and probably
also Glulx, at some point).  The intent is to provide a feature set roughly
comparable to Caml Light, including:

   * Hindley-Milner static type system with type inference
   * Mark/sweep/compact GC
   * Closures
   * Tail-call optimization
   * Arrays, lists, tuples, records
   * Variant types
   * Pattern matching
   * Parametric polymorphism

Think "OCaml, but without objects, modules, polymorphic variants, or labels."

This project is very incomplete and should not be considered "useful" at this
point in time.  But some of the harder problems have already been solved, and
some toy programs can be compiled successfully.


LICENSE
=======

The compiler is licensed under the GPL version 2; see LICENSE.COMPILER for
details.

The runtime library is licensed under a simplified BSD license; see
LICENSE.RUNTIME-LIB for details.


