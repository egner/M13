# Versuch, die Generierung einer Stabilisatorkette
# zu automatisieren, MP, 29.10.96


if not IsBound(EnumeratePermGroup) then
  Read("asc.g");
fi;
if not IsBound(movedPointsSets) then
  Read("findbase.g");
fi;

# Hilfsfunktionen
# ===============

# setify( <list> ) sortiert die Liste und entfernt doppelte
#   ohne eine neue Liste zu erzeugen

setify := function ( list )
  local rd, wr;

  if Length(list) < 2 then
    return;
  fi;
  Sort(list);
  wr := 1;
  for rd in [2..Length(list)] do
    if list[rd] <> list[wr] then
      wr       := wr + 1;
      list[wr] := list[rd];
    fi;
  od;
  while wr < Length(list) do
    wr := wr + 1;
    Unbind(list[wr]);
  od;
end;


# makepairslist( <permgroup>, <baselist> )
#   macht aus der baselist eine Liste von Paaren [Wort, Permutation]

makepairsbaselist := function ( G, baselist )
  local L;

  L := Filtered(baselist, p -> p[1] <> "finalpart");
  return 
    List(
      L, 
      p -> [p[1], MappedWord(p[1], G.abstractGenerators, G.generators)]
   );
end;


# extractbase( <baselist>)
#    holt die Basis aus der baselist

extractbase := function ( baselist )
  return Reversed(Concatenation(List(baselist, p -> p[2])));
end;


# lengthprofile( <baselist> )
#    erstellt das Wortl"angenprofil einer baselist 

lengthprofile := function ( baselist )
  local L;

  L := Filtered(baselist, p -> p[1] <> "finalpart");
  return List(L, p -> LengthWord(p[1]));
end;


# Elemente zum schnellen F"ullen der Stabchain
# ============================================

#F insertConjugates( <permgroup>, <maxLength> )
#F   calculates the maxLength shortest words in 
#F     G.lazyPairs^G.shortPairs
#F   for each place in the abstractStabChain, which has to be
#F   present. The so built table[level][coset] is written to the
#F   the field G.conjugatedTable.

insertConjugates := function ( G, maxLength )
  local 
    A,      # G.abstractStabChain
    base,   # A.base
    points, # [1..largest moved point of G]
    table,  # the table to be calculated
    len,    # Length(G.lazyPairs)
    il,     # counter in G.lazyPairs
    lp,     # G.lazyPairs
    sp,     # G.shortPairs
    cpWord, # word in G.lazyPairs^G.shortPairs
    cpPerm, # perm to cpWord
    level,  # level in stabchain
    coset,  # coset in level
    t, i;   # counter

  A      := G.abstractStabChain;
  base   := A.base;
  points := [1..Maximum(PermGroupOps.MovedPoints(G))];

  # prepare table
  table  := 
    List(
      [1..Length(base)], 
      level -> List(points, point -> [ ])
    );


  len := Length(G.lazyPairs);
  Print("#I counting until ",len,"\n");
  for il in [1..len] do
    lp := G.lazyPairs[il];
    for sp in G.shortPairs do
      cpWord := lp[1]^sp[1];
      cpPerm := lp[2]^sp[2];

      # calculate level for the word
      level := 1;
      while 
        level < Length(base) and 
        base[level]^cpPerm = base[level] 
      do
        level := level+1;
      od;

      # calculate coset in the level
      coset := base[level]^cpPerm;

      # add word
      t := table[level][coset];
      Add(t, cpWord);

      # if the list exceeds 10*maxLength elements, 
      # reduce to the maxLength shortest
      if Length(t) > 10*maxLength then
        setify(t);
        for i in [maxLength+1..Length(t)] do
          Unbind(t[i]);
        od;
      fi;
    od; # shortPairs
    if il mod 10 = 0 then
      Print(il, " \c");
    fi;
  od; # lazyPairs

  # reduce to the maxLength shortest in each place
  for level in [1..Length(base)] do
    for coset in points do
      t := table[level][coset];
      setify(t);
      for i in [maxLength+1..Length(t)] do
        Unbind(t[i]);
      od;
    od;
  od;
  Print("\n");

  # write result to G.conjugatedTable
  G.conjugatedTable := table;
end;


# Automatische Generierung einer Abstract Stabchain
# =================================================

#F AbstractStabChainGenerationAllStrategies( 
#F   <permgroup>, <nr-of-shortPairs>, <final-part-of-base> )
#F
#F   calculates an abstract stabchain by enumeration of 
#F   nr-of-shortPairs shortest word in the abstract generators.
#F   A list of points can be forced to be the deepest part in
#F   the corresponding base by final-part-of-base.
#F   Note that the algorithm does not necessarily produce
#F   a full stabchain. 

# The algorithm:
#   1. Enumeration of nrSP shortest words
#   2. Generation of lazy elements
#   3. Calculation of all moved points sets obtained by
#      shortElements^lazyElements
#   4. Calculating baselists according to all strategies
#      which are given by the different lengths of words
#      occuring in G.movedPointsList.
#   5. Calculating the quality of each baselist by the 
#      weighted sum (by depth) of wordlengths in baselist.
#   6. Choosing best baselist, that is the baselist with
#      smallest quality.
#   7. Creating initial stabchain and calculation of 
#      conjugated elements, that is maximal 10 elements
#      out of shortElements^lazyElements for each place in 
#      the stabchain.
#   8. Inserting baselist.
#   9. Inserting short elements.
#  10. Riesel from bottom to top.
#  11. Inserting conjugated elements.
#  12. Riesel from bottom to top.

AbstractStabChainGenerationAllStrategies := 
  function ( G , nrSP, finalpartofbase )

  local 
    nrofstrats,    # number of possible strategies to calculate baselist
    allbaselists,  # list of baselists to all strategies
    maxlen,        # maximal length of a baselist in allbaselists
    longbaselists, # sublist of longest baselists in allbaselists
    lenprofile,    # lengthprofile of the baselists
    quality,       # quality of longbaselists
    bestbaselist,  # one best baselist
    beststrats,    # all best strategies
    base,          # base to bestbaselist
    A,             # G.abstractStabChain
    ins,           # Insert
    rie,           # Riesel
    i;             # counter

  Print("\nSTEP 1: Enumeration of the ",nrSP," shortest words\n");
  Print("==============================================\n\n");
  EnumeratePermGroup(G, nrSP);

  Print("\nSTEP 2: Generation of lazy elements\n");
  Print("===================================\n\n");
  MakeLazyPairs(G);

  Print("\nSTEP 3: Calculation of moved points sets with shortest words\n");
  Print("============================================================\n\n");
  movedPointsSets(G);
  nrofstrats := LengthWord(G.movedPointsList[Length(G.movedPointsList)][1]);
  
  Print("\nSTEP 4: Calculating baselists with ",nrofstrats," strategies\n");
  Print("================================================\n\n");
  allbaselists  := findbaseall(G, finalpartofbase);
  maxlen        := Maximum(List(allbaselists, Length));
  longbaselists := Filtered(allbaselists, l -> Length(l) = maxlen);
  lenprofile    := List(longbaselists, lengthprofile);
  quality       := 
    List(
      lenprofile, 
      l -> Sum(List([1..Length(l)], i -> (Length(l) + 1 - i)*l[i]))
    );
  Print("\n#I weighted sum of wordlengths in longest baselists: ",quality,"\n");

  Print("\nSTEP 5: Choosing best baselist\n");
  Print("==============================\n\n");
  bestbaselist := longbaselists[Position(quality, Minimum(quality))];
  beststrats   := 
    Filtered(
      [1..nrofstrats], 
      i -> allbaselists[i] = bestbaselist
    );
  Print("#I best strategies are: ",beststrats,"\n");
  base := extractbase(bestbaselist);
  Print("#I best baselist:\n",bestbaselist,"\n");
  Print("#I base: ",base,"\n");

  Print("\nSTEP 6: Creating initial stabchain\n");
  Print("==================================\n\n");
  ASCOps.New(G, 10, base);
  A := G.abstractStabChain;
  Print(A);
  ins  := x -> ASCOps.Insert(G, x);
  rie  := i -> ASCOps.InsertCollisionPairs(G, i);

  Print("\nSTEP 7: Calculating conjugates for each place in stabchain\n");
  Print("==========================================================\n\n");
  insertConjugates(G, 10);

  Print("\nSTEP 8: Inserting baselist\n");
  Print("==========================\n\n");
  ins(makepairsbaselist(G, bestbaselist));
  Print(A);

  Print("\nSTEP 9: Inserting short pairs\n");
  Print("=============================\n\n");
  ins(G.shortPairs);
  Print(A);

  Print("\nSTEP 10: Riesel from the bottom to the top\n");
  Print("==========================================\n\n");
  for i in [Length(A.base), Length(A.base)-1..1] do   
    rie(i);
  od;
  Print(A);

  Print("\nSTEP 11: Inserting conjugated pairs\n");
  Print("===================================\n\n");  
  ins(Flat(G.conjugatedTable));
  Print(A);

  Print("\nSTEP 12: Riesel from the bottom to the top\n");
  Print("==========================================\n\n");
  for i in [Length(A.base), Length(A.base)-1..1] do   
    rie(i);
  od;

  Print("\n=======\n");
  Print("RESULT:\n");
  Print("=======\n\n");

  return A;  

end;

#F AbstractStabChainGenerationOneStrategies( 
#F   <permgroup>, <nr-of-shortPairs>, <final-part-of-base> )
#F   
#F   does the same as AbstractStabChainGenerationAllStrategies, 
#F   but uses only one strategy for calculation of the baselist.
#F

AbstractStabChainGenerationOneStrategy := 
  function ( G , nrSP, finalpartofbase )

  local 
    baselist, # baselist computed
    base,     # corresponding base
    A,        # G.abstractStabChain
    ins,      # Insert
    rie,      # Riesel
    i;        # counter

  Print("\nSTEP 1: Enumeration of the ",nrSP," shortest words\n");
  Print("==============================================\n\n");
  EnumeratePermGroup(G, nrSP);

  Print("\nSTEP 2: Generation of lazy elements\n");
  Print("===================================\n\n");
  MakeLazyPairs(G);

  Print("\nSTEP 3: Calculation of moved points sets with shortest words\n");
  Print("============================================================\n\n");
  movedPointsSets(G);
  
  Print("\nSTEP 4: Calculating baselist\n");
  Print("============================\n\n");
  baselist := findbase(G, 1, finalpartofbase);

  base := extractbase(baselist);
  Print("#I baselist:\n",baselist,"\n");
  Print("#I base: ",base,"\n");

  Print("\nSTEP 6: Creating initial stabchain\n");
  Print("==================================\n\n");
  ASCOps.New(G, 10, base);
  A := G.abstractStabChain;
  Print(A);
  ins  := x -> ASCOps.Insert(G, x);
  rie  := i -> ASCOps.InsertCollisionPairs(G, i);

  Print("\nSTEP 7: Calculating conjugates for each place in stabchain\n");
  Print("==========================================================\n\n");
  insertConjugates(G, 10);

  Print("\nSTEP 8: Inserting baselist\n");
  Print("==========================\n\n");
  ins(makepairsbaselist(G, baselist));
  Print(A);

  Print("\nSTEP 9: Inserting conjugated pairs\n");
  Print("===================================\n\n");  
  ins(Flat(G.conjugatedTable));
  Print(A);

  Print("\nSTEP 10: Riesel from the bottom to the top\n");
  Print("==========================================\n\n");
  for i in [Length(A.base), Length(A.base)-1..1] do   
    rie(i);
  od;
  Print(A);

  Print("\nSTEP 11: Inserting short pairs\n");
  Print("==============================\n\n");
  ins(G.shortPairs);
  Print(A);

  Print("\nSTEP 12: Riesel from the bottom to the top\n");
  Print("==========================================\n\n");
  for i in [Length(A.base), Length(A.base)-1..1] do   
    rie(i);
  od;

  Print("\n=======\n");
  Print("RESULT:\n");
  Print("=======\n\n");

  return A;  

end;
