# AbstractStabChain in C-Format ausgeben, SE, 7.8.97, GAP v3.4

# Specification of the output produced
# ====================================
#
# int nrPoints;
#   /* The degree of the permutation group. The points
#      are numbered [0..nrPoints-1].
#   */
#
# int nrBasepoints;
# int basepoints[];
#   /* The base points. */
#
# int nrGenerators;
# int generators[][];
#   /* The permutations which are the generators. The
#      generators g are numbered [1..nrGenerators].
#      (To allow inverse powers in the words!) 
#      Generator g maps the point p to the point
#        generators[g-1][p].
#   */
#
# int transversals[][][];
# int words[][][];
#   /* The transversals and their corresponding words
#      in the generators. transversals[level][im] is a
#      permutation, that is maps point p into
#        transversals[level][im][p].
#      In particular, transversals[level][im] stabilizes
#      all points basepoints[0], .., basepoints[level-1]
#      and maps basepoints[level] into the image point im.
#      The permutation transversals[level][im] has been
#      factored into the word 
#        words[level][im].
#      The word is a 0-terminated list of the generators g
#      or the inverse generators -g which form the word
#      in the abstract generators. An entry which is not
#      in the orbit of basepoints[level] is written as
#        transversals[level][im] = { -1, .., -1 };
#        words[level][im] = { 0 };
#    */

#F GetASC( <permgrp> )
#F   extracts the low-level information about the abstract
#F   stabChain provided in <permgrp>.
#F

GetASC := function ( G )
  local R, A, T, level, points, wx, p;

  if not IsBound(G.abstractStabChain) then
    Error("<G> must have an abstractStabChain");
  fi;
  A := G.abstractStabChain;

  # extract information
  R := rec( );

  R.nrPoints := 
    PermGroupOps.LargestMovedPoint(G);

  R.basepoints := 
    A.base;
 
  R.generators         := G.generators;
  R.abstractGenerators := G.abstractGenerators;

  R.transversals := [ ];
  R.words        := [ ];
  for level in [1..Length(R.basepoints)] do
    R.transversals[level] := List([1..R.nrPoints], p -> false);
    R.words[level]        := List([1..R.nrPoints], p -> false);
    for wx in ASCOps.TransversalOrbitGraph(G, level) do
      p := R.basepoints[level]^wx[2];
      R.transversals[level][p] := wx[2];
      R.words[level][p]        := wx[1];
    od;
  od;

  return R;
end;

PrintASCToC := function ( filename, R )
  local print, printListInline, printList;

  printListInline := function ( x, print )
    local i;

    Print("{");
    for i in [1..Length(x)] do
      print(x[i]);
      if i < Length(x) then
        Print(", ");
      fi;
    od;
    Print("}");
  end;

  printList := function ( x, print, indent )
    local i, k;

    Print("{ ");
    for i in [1..Length(x)] do
      print(x[i]);
      if i < Length(x) then
        Print(",\n");
        for k in [1..indent+2] do
          Print(" ");
        od;
      fi;
    od;
    Print("\n");
    for k in [1..indent] do
      Print(" ");
    od;
    Print("}");
  end;

  print := function ( R )
    local ags, agsInv;

    ags    := R.abstractGenerators;
    agsInv := List(ags, g -> g^-1);

    Print("int nrPoints = ", R.nrPoints, ";\n\n");

    Print("int nrBasepoints = ", Length(R.basepoints), ";\n");

    Print("int basepoints[] = ");
    printListInline(R.basepoints-1, Print);
    Print(";\n\n");

    Print("int nrGenerators   = ", Length(R.generators), ";\n");

    Print("int generators[][] =\n  ");
    printList(
      R.generators,
      function ( perm )
        printListInline(
          OnTuples([1..R.nrPoints], perm)-1,
          Print
        );
      end,
      2
    );
    Print(";\n\n");

    Print("int transversals[][][] =\n  ");
    printList(
      R.transversals, 
      function ( t )
        printList(
          t, 
          function ( perm )
            if perm = false then
              printListInline(
                List([1..R.nrPoints], i -> -1),
                Print
              );
            else
              printListInline(
                OnTuples([1..R.nrPoints], perm)-1, 
                Print
              );
            fi;
          end,
          4
        );
      end,
      2
    );
    Print(";\n\n");

    Print("int words[][][] =\n  ");
    printList(
      R.words,
      function ( t )
        printList(
          t, 
          function ( word )
            local w, i, wi;

            w := [ ];
            if word <> false then
	      for i in [1..LengthWord(word)] do
		wi := Subword(word, i, i);
		if wi in ags then 
		  Add(w, Position(ags, wi));
		elif wi in agsInv then
		  Add(w, -Position(agsInv, wi));
		else
		  Error("<wi> not in <R>.abstractGenerators");
		fi;
	      od;
            fi;
            Add(w, 0);

            printListInline(w, Print);
          end,
          4
        );
      end,
      2
    );
    Print(";\n\n");
    return "";
  end;

  if IsPermGroup(R) then
    R := GetASC(R);
  fi;

  PrintTo(filename, print(R));
end;

