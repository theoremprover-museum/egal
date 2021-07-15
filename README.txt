Egal is an open source mathematical proof checker.

If you think you might be interested in it, you're probably wrong.  It
was intended for the distributed construction of a library of
formalized mathematics, and most people don't care about that.

Information about how to install it is in INSTALL.

The open source license is in LICENSE.

Some formal documents building up the fundamental building blocks of
mathematics are in the formaldocs subdirectory.

A manual is in the doc subdirectory: doc/egalmanual.pdf

In the doc subdirectory you will also find the following:

. zermelo1908memo.pdf : This corresponds more or less to the
  formalization of Zermelo's 1908 proof of the Well-Ordering Theorem
  in Zermelo1908.mg (in formaldocs).

. pairfunsets.pdf : This corresponds to a number of the formalizations
  found in EpsInd.mg, DisjointUnions.mg, OrderedPairs.mg, DepSums.mg,
  FuncsSets.mg and DepProds.mg (in formaldocs).

. msethoas.pdf : This is a report that might help someone who might
  want to modify Egal to reason about programs using higher-order
  abstract syntax to represent bound variables conveniently.

The code was used to run a bitcoin treasure hunt in the summer of
2014. The corresponding formal documents can be found in the
formaldocs subdirectory as well. The treasure hunt is now over, but I
am including one new document without proofs corresponding to some
final treasures. I will never release the solutions. The new document
is formaldocs/CategoryProblems.mg and depends on
formaldocs/CategoryPreamble.mgs.

If you have the code because you're looking for these bitcoin
treasures, then try this:

./makebytecode
cd formaldocs
ocamlrun ../bin/egal.bytecode -ind IndexMar2014 -I CategoryPreamble.mgs CategoryProblems.mg

You'll need to edit CategoryProblems.mg by replacing "Admitted." with proofs.

To see what solutions look like, compare formaldocs/ExEq1Problems.mg to formaldocs/ExEq1.mg.

If you decide you'd like to help me develop it, then please just take
the code and start developing it.  I won't do anymore implementation
work on this.  Here are some ideas I had planned to implement.

1. In terms of the architecture, Egal could be split into 3 different
parts. The core part would only have the nameless terms and would not
need a parser and printer.  A second part would include the parser and
printer and would allow users to give terms and proofs using
mathematical expressions. Finally a third part would handle proof
tactics. Also, there are various things hardcoded into mgcheck.ml that
really shouldn't be, e.g., the global names of Tarski-Groethendieck
axioms.

2. Egal would make sense as part of a peer-to-peer network (like
ProofPeer is planned to be, see proofpeer.net) in which people could
request proofs or even put bounties on conjectures (like
proofmarket.org).

3. Egal could benefit from automation.  The higher-order theorem
prover Satallax I wrote could be used to produce Egal proof terms with
reasonably little effort.  In addition, a dependent type theory like
the one underlying Coq can be embedded into TG set theory. Indeed this
was the motiviation for the nonstandard representations of functions
and pairs in formaldocs.  This means one could formalize some things
in Coq with the type checking and automation Coq provides and then
automatically translate the results to Egal.

4. The technology could be used for more than mathematical proofs.
For example, it could be applied to program verification or proof
carrying code.

As noted above, I had planned to pursue these ideas, but I've decided
against doing more significant implementation work.  In my opinion,
there isn't enough interest to justify the effort.
