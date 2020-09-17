# Tools fuer Permutationen, SE, MP, 12.--30.4.96

InfoASC1 := Print;

# Tools for Permutations
# ======================

#F NrMovedPointsPerm( <perm> ) 
#F   returns the number of moved points of a permutation.
#F

NrMovedPointsPerm := function (s)
  local n, i;

  if s = s^0 then
    return 0;
  fi;
  n := 0;
  for i in [SmallestMovedPointPerm(s)..LargestMovedPointPerm(s)] do
    if i^s <> i then
      n := n + 1;
    fi;
  od;
  return n;
end;

#F MovedPointsPerm( <perm> ) 
#F   returns the set of moved points of a permutation.
#F

MovedPointsPerm := function (s)
  local mp, n, i;

  if s = s^0 then
    return [];
  fi;
  mp := [ ];
  for i in [SmallestMovedPointPerm(s)..LargestMovedPointPerm(s)] do
    if i^s <> i then
      Add(mp, i);
    fi;
  od;
  return mp;
end;

#F HashPerm( <max>, <perm> )
#F   returns a hashing value in [1..max] for the perm.
#F   Prefer a prime for max for good performance.
#F

HashPerm := function ( max, perm )
  local hash, base, point;

  # The hashing value is computed as using the vector of image
  # points as coefficients of a mixed basis representation.
  # Finally the result is mapped into the output range with mod.
  # The method seems to be reasonable (no formal analysis done).

  if perm = () then
    return 1;
  fi;
  hash := 0;
  base := 1;
  for point in [1..LargestMovedPointPerm(perm)] do
    base := RemInt(base * point, max);
    hash := hash + (point^perm - 1) * base;
  od;
  return RemInt(hash, max)+1;
end;

HashPerm1 := function ( max, perm )
  local hash, digit, degree, i;

  # The hashing value is computed as using the vector of image
  # points as coefficients of a mixed basis representation.
  # Finally the result is mapped into the output range with mod.
  # The method seems to be reasonable (no formal analysis done).

  if perm = () then
    return 1;
  fi;

  digit  := [ ];
  degree := LargestMovedPointPerm(perm);
  i      := degree;
  while i >= 1 do
    digit[i] := i - i^perm;
    if digit[i] > 0 then 
      perm := perm * (i^perm, i);
    fi;
    i := i - 1;
  od;

  hash := 0;
  for i in [degree, degree-1 .. 2] do
    hash := RemInt(hash*i + digit[i], max);
  od;
  return hash + 1;
end;

# Universal tools
# ===============

# SqueezeList( <list-with-holes> )
#   removes the holes from the list.
#

SqueezeList := function ( list )
  local len, rd, wr;

  len := Length(list);
  wr  := 1;
  for rd in [1..len] do
    if IsBound(list[rd]) then
      if rd > wr then
        list[wr] := list[rd];
      fi;
      wr := wr + 1;
    fi;
  od;
  while wr <= len do
    if IsBound(list[wr]) then
      Unbind(list[wr]);
    fi;
    wr := wr + 1;
  od;
end;

# ListSqueezed( <list-with-holes>, <function> )
#   is like List but removes the holes from the list.
#

ListSqueezed := function ( list, func )
  list := ShallowCopy(list);
  SqueezeList(list);
  return List(list, func);
end;

# Orderly generation of short [word, perm]-pairs
# ==============================================

if not IsBound(InfoASC1) then
  InfoASC1 := Ignore;
fi;

#F MakeGeneratorPairs( <group> )
#F   adds a field G.abstractGenerators if it is not present
#F   and computes a field G.generatorPairs which contains
#F   the set of pairs [w, e] where w is an abstract generator
#F   or an inverse abstract generator and e is the corresponding
#F   element of the group. The elements are all distinct, the
#F   corresponding words are chosen smallest. Note that the
#F   list G.abstractGenerators may also contain words.
#F

MakeGeneratorPairs := function ( G )
  local gps, gps1, x, y, i;

  if IsBound(G.generatorPairs) then
    return;
  fi;
  if not IsBound(G.abstractGenerators) then
    G.abstractGenerators :=
      AbstractGenerators("g", Length(G.generators));
    InfoASC1(
      "#I G.abstractGenerators := ", G.abstractGenerators, "\n"
    );
  fi;

  # all pairs [element, word] consider
  gps := [ ];
  for i in [1..Length(G.generators)] do
    Add(gps, [ G.generators[i],    G.abstractGenerators[i]    ]);
    Add(gps, [ G.generators[i]^-1, G.abstractGenerators[i]^-1 ]);
  od;

  # remove redundant elements
  Sort(gps);
  x    := gps[1];
  gps1 := [ ];
  for y in gps do
    if y[1] <> x[1] then
      Add(gps1, x);
      x := y;
    fi;
  od;
  Add(gps1, x);

  # store [word, element] pairs
  G.generatorPairs := Set(List(gps1, x -> [ x[2], x[1] ]));
  InfoASC1(
    "#I G.generatorPairs := ", G.generatorPairs, "\n"
  );
end;


#F EnumeratePermGroup( <permgroup> [, <nrElements>] )
#F   enumerates the group up to nrElements. If nrElements
#F   is omitted then [1000..10000] elements are produced
#F   such that the largest length is completed.
#F     The group-words in G.generators and G.abstractGenerators 
#F   are generated in order (with respect to the order on *words* 
#F   as defined by GAP) and stored. The function returns nothing.
#F   Note that G.abstractGenerators may well contain words.
#F   The result of the enumeration is stored as
#F
#F   G.shortPairs
#F     a set of pairs [word, perm] which contains the
#F     specified number of shortest elements of the group.
#F     In particular word is the unique minimal word in the
#F     given abstract generators which represents perm.
#F

EnumeratePermGroup := function ( arg )
  local
    G,             # the group to enumerate
    nrElements,    # number of elements to generate
    wordGens,      # flag if G.abstractGenerators contains words
    border,        # priority queue for the border to expand
    first,         # index of first element of border
    maxFirst,      # max. number of leading holes in border
    table,         # list with holes indexed by hash value of lists of pairs
    maxTable,      # [1..maxTable] is range of hash values
    size,          # number of elements in table
    minSize,       # minimum number of elements if nrElements = "automatic"
    maxSize,       # maximum number of elements if nrElements = "automatic"
    lengths,       # lengths[k] is number of elements of length k
    nextLength,    # prediction of lengths[Length(lengths)+1]
    printedLength, # maximal k such that lengths[k] has been printed
    x, g,          # [word, perm], [abstr. gen., gen.]
    xg, xg2,       # product x*g; 2nd component
    h;             # hash value for x*g

  # parameter defaults
  minSize  := 1000;
  maxSize  := 10000;
  maxTable := 10007; # or 997 (primes around 10^4 or 10^3)
  maxFirst := 100;

  if Length(arg) = 1 and IsPermGroup(arg[1]) then
    G          := arg[1];
    nrElements := "automatic";
  elif Length(arg) = 2 and IsPermGroup(arg[1]) and IsInt(arg[2]) then
    G          := arg[1];
    nrElements := arg[2];
    if nrElements < 1 then
      Error("nrElements must be positive");
    fi;
  else
    Error("usage: EnumeratePermGroup( <permgroup> [, <nrElements>] )");
  fi;
  MakeGeneratorPairs(G);

  # recognize if words of words are to be generated
  wordGens := ForAny(G.generatorPairs, x -> LengthWord(x[1]) > 1);
  if wordGens and nrElements = "automatic" then
    nrElements := minSize;
  fi;

  InfoASC1(
    "#I EnumeratePermGroup uses hash table of size ", maxTable, "\n"
  );
  if not wordGens then 
    InfoASC1("#I   exactly 1 permutation of length 0\n");
  fi;

  # initialize hash table
  table := [ ];
  if nrElements <> "automatic" then
    maxTable := nrElements;
    while maxTable > 1 and not IsPrimeInt(maxTable) do
      maxTable := maxTable - 1;
    od;
  fi;
  table[ HashPerm(maxTable, ()) ] := [ [IdWord, ()] ];
  size          := 1;
  lengths       := [ ];
  nextLength    := 1;
  printedLength := 0;

  # initialize border
  border   := [ [IdWord, ()] ];
  first    := 1;

  # orderly generation of [word, perm]-pairs
  while IsBound(border[first]) and size < nrElements do

    # get x as first in border
    x := border[first];
    Unbind(border[first]);
    first := first + 1;
    if first > maxFirst or not IsBound(border[first]) then
      SqueezeList(border);
      first  := 1;
    fi;

    # expand x in every direction g
    for g in G.generatorPairs do
      
      # check if x*g has been generated before
      xg2 := x[2] * g[2];
      h   := HashPerm(maxTable, xg2);
      if 
        not IsBound(table[h]) or 
        ForAll(table[h], y -> y[2] <> xg2) 
      then

        # add x*g to the table
        xg := [ x[1] * g[1], xg2 ];     
        if not IsBound(table[h]) then
          table[h] := [ ];
        fi;
        Add(table[h], xg);
        Add(border, xg);
        size := size + 1;
        if LengthWord(xg[1]) > Length(lengths) then

          # step to next length for the elements
          while LengthWord(xg[1]) > Length(lengths)+1 do
            Add(lengths, 0);
          od;
          Add(lengths, 1);

          # predict final value of lengths[Length(lengths)]
          if Length(lengths) = 1 then
            nextLength := Length(G.generatorPairs);
          elif Length(lengths) = 2 then
            nextLength := nextLength * (nextLength - 1);
          elif lengths[Length(lengths)-2] > 0 then
        nextLength := 
          QuoInt(
        lengths[Length(lengths)-1]^2, 
        lengths[Length(lengths)-2]
          );
          fi;

          # print information on the lengths
          if Length(lengths) > 1 and not wordGens then
            while printedLength < Length(lengths)-2 do
              printedLength := printedLength + 1;
              InfoASC1(
            "#I   exactly ", lengths[printedLength],
            " permutations of length ", printedLength, "\n"
          );
            od;
            printedLength := printedLength + 1;
            InfoASC1(
              "#I   exactly ", lengths[printedLength],
          " permutations of length ", printedLength,
              " (predicting ", nextLength, " for next length)\n"
            );
          fi;

        else

          # simply count xg in lengths
          if LengthWord(xg[1]) > 0 then
            lengths[LengthWord(xg[1])] := lengths[LengthWord(xg[1])] + 1;
          fi;
        fi;

        # check if enough elements have been generated
        if 
          nrElements = "automatic" and lengths[Length(lengths)] = 1 and
            size > minSize and size + nextLength > maxSize or
          IsInt(nrElements) and 
            size >= nrElements
        then

      # make the set of pairs
      G.shortPairs := Concatenation(table);
      Sort(G.shortPairs);
          if nrElements = "automatic" and Number(border) > 0 then

            # remove the single element of largest length
            Unbind(G.shortPairs[Length(G.shortPairs)]);
          fi;
      IsSet(G.shortPairs);

          return;
        fi;
      fi;
    od;
  od;

  # make the set of pairs
  G.shortPairs := Concatenation(table);
  Sort(G.shortPairs);
  if 
    nrElements = "automatic" and 
    Number(border) > 0 and
    lengths[Length(lengths)] = 1 and
    LengthWord(G.shortPairs[Length(G.shortPairs)][1]) = 
      Length(lengths)
  then
    Unbind(G.shortPairs[Length(G.shortPairs)]);
  fi;
  IsSet(G.shortPairs);
end;
  

# Lazy elements (= permutations with many fixed points)
# =====================================================

#F SortLazyPairs( <list> )
#F   sorts the given list of permutations or [word, perm]-pairs
#F   with respect to the number of moved points such that the
#F   elements with many fixed points are in front. The function
#F   returns nothing, it is only called for its side-effects.
#F

SortLazyElements := function ( list )
  local mp;

  if Length(list) = 0 then
    return [ ];
  fi;
  if IsPerm(list[1]) then
    mp := List(list, NrMovedPointsPerm);
  elif IsList(list[1]) and IsPerm(list[1][2]) then
    mp := List(list, x -> NrMovedPointsPerm(x[2]));
  else
    Error("usage: SortLazyElements( <list-of-perm/[word, perm]> )");
  fi;
  SortParallel(mp, list);
end;

#F MakeLazyPairs( <permgroup> )
#F   collects a list of short and lazy pairs (= few moved points).
#F   Lazy pairs are good candidates for being conjugated in order
#F   to reach deep levels in the stabilizer chain of G, later on.
#F   The list is computed, sorted (lazy ones in front) and bound
#F   to the field G.lazyPairs. The function returns nothing, it
#F   is called for its side effects. There are two sources
#F     (1) G.shortPairs as computed by EnumeratePermGroup(G).
#F         Preferably G.shortPairs contains *all* elements of
#F         the largest length.
#F     (2) The elements of G.shortPairs extended by suitable
#F         powers of the generators such that the result has
#F         vanishing exponent sum in all abstract generators.
#F   Comments
#F     * The non-trivial elements of G.shortPairs which do not
#F       move all points (not lazy) and which are not conjugate
#F       to shorter words (not of the form x^-1 w x) are good
#F       candidates for being lazy, short and produce few
#F       collisions when conjugated.
#F     * Assuming that the generators of G move substantially
#F       fewer points than random elements of G then it is a
#F       good idea to consider words of vanishing exponent sum
#F       with respect to all abstract generators. In order to
#F       construct these elements we enumerate the group H
#F       generated by the commutators of generators of G (in 
#F       general *not* the commutator subgroup of G). These
#F       elements are filtered like the ones of G.shortPairs.
#F

MakeLazyPairs := function ( G )
  local 
    lazy, lazy1, # lazy pairs, a copy
    comms, H,    # commutators of generators of G, H = <comms>
    mG,          # number of points moved by the group
    nG,          # largest length of word in G.shortPairs
    m,           # number of moved points of x[2]
    n,           # length of x[1]
    x, y,        # [word, perm]-pairs
    i,           # counter for generator pairs [wi, ei]
    wi, ei,      # abstract generator i, generator i
    ni;          # exponent sum of wi in y

  MakeGeneratorPairs(G);
  if not IsBound(G.shortPairs) then
    EnumeratePermGroup(G);
  fi;
  mG := PermGroupOps.NrMovedPoints(G);
  nG := LengthWord(G.shortPairs[Length(G.shortPairs)][1]);

  # collect lazy pairs from G.shortPairs
  InfoASC1(
    "#I MakeLazyPairs called using ", 
    Length(G.shortPairs), " short pairs\n"
  );
  lazy := [ ];
  for x in G.shortPairs do

    # only add x if not all points are moved
    m := NrMovedPointsPerm(x[2]);
    n := LengthWord(x[1]);
    if
      0 < m and m < mG and 
      Subword(x[1], 1, 1) <> Subword(x[1], n, n)^-1
    then
      Add(lazy, [ m, x[2], x[1] ]);
    fi;
  od;

  # add completed pairs to lazy
  InfoASC1("#I   adding completed words\n");
  comms :=
    Filtered(
      lazy, 
      x -> 
        LengthWord(x[3]) = 4 and 
        x[3] < x[3]^-1 and
        ForAll(G.abstractGenerators, g -> ExponentSumWord(x[3], g) = 0)
    );
  H := Group(List(comms, x -> x[2]), ());
  H.abstractGenerators := List(comms, x -> x[3]);
  if Length(H.generators) = 0 then
    H.shortPairs := [ ];
  else
    EnumeratePermGroup(H, Length(lazy));
  fi;
  for x in H.shortPairs do
    # only add x if not all points are moved
    m := NrMovedPointsPerm(x[2]);
    n := LengthWord(x[1]);
    if
      0 < m and m < mG and 
      n > nG and
      Subword(x[1], 1, 1) <> Subword(x[1], n, n)^-1
    then
      Add(lazy, [ m, x[2], x[1] ]);
    fi;
  od;

  # remove duplicate words for the same perm
  InfoASC1("#I   removing duplicates\n");
  Sort(lazy);
  lazy1 := [ ];
  x     := lazy[1];
  for y in lazy do
    if y[2] <> x[2] then
      Add(lazy1, x);
      x := y;
    fi;
  od;
  Add(lazy1, x);
  lazy := lazy1;

  # sort by number of moved points
  InfoASC1("#I   sorting ", Length(lazy), " pairs for laziness\n");
  G.lazyPairs := List(lazy, x -> [ x[3], x[2] ]);
  SortLazyElements(G.lazyPairs);
end;


# Heuristic choice of base
# ========================

#F HeuristicBase( <permgroup>, <list-of-int> )
#F   chooses a base for the group G such that the given
#F   list of integers is the initial base segment and the
#F   base is heuristically completed using the elements in
#F   G.shortPairs as generated by EnumeratePermGroup.
#F

HeuristicBase := function ( G, initialBaseSegment )
  local
    base,    # the chosen base; result
    points,  # moved points sorted by decreasing quality
    quality, # quality: large n, low s/n
    p,       # a point moved by G
    n,       # number of fixing elements of p
    s,       # sum of lengths of fixing elements of p
    we,      # [word, element]-pair in shortPairs
    format;  # function to print right-aligned

  # base as proposed from shortPairs
  if false and # ...off
IsBound(G.shortPairs) then
    InfoASC1(
      "#I HeuristicBase called with ", Length(G.shortPairs), " words\n",
      "#I   point  (nr. fixing words) (sum length) (avg. length)  quality\n"
    );
    format := function (width, x)
      x := String(x);
      while LengthString(x) < width do
        x := ConcatenationString(" ", x);
      od;
      return x;
    end;
    points := [ ];
    for p in Set( PermGroupOps.MovedPoints(G) ) do
      n := 0;
      s := 0;
      for we in G.shortPairs do
        if p^we[2] = p then
          n := n + 1;
          s := s + LengthWord(we[1]);
        fi;
      od;
      if n = 0 or s = 0 then
        quality := 0;
        InfoASC1(
          "#I   ", format(5, p), "  ", format(18, n), " ", format(12, s), " ", 
          "    undefined", "  ", format(7, quality), "\n"
        );
      else
       quality := n * 1/(s/n);
        InfoASC1(
          "#I   ", format(5, p), "  ", format(18, n), " ", format(12, s), " ", 
          format(13, QuoInt(s, n)), "  ", format(7, quality), "\n"
        );
      fi;
      Add(points, [ -quality, p ]);
    od;
    Sort(points);
    points := List(points, qp -> qp[2]);
  else
    points := PermGroupOps.MovedPoints(G);
  fi;

  # merging initialBaseSegment and points
  base := [ ];
  for p in initialBaseSegment do
    if p in points and not p in base then
      Add(base, p);
    fi;
  od;
  for p in points do
    if not p in base then
      Add(base, p);
    fi;
  od;
  if IsBound(G.shortPairs) > 0 then
    InfoASC1("#I   choosing base ", base, "\n");
  fi;
  return base;
end;

# Production of random [word, element]-pairs
# ==========================================

# choose random *word* (unlikely to be uniform over G)
RandomPair := function ( G, length )
  local w, e, g;

  MakeGeneratorPairs(G);
  w := IdWord;
  e := ();
  while LengthWord(w) < length do
    g := Random(G.generatorPairs);
    w := w * g[1];
    e := e * g[2];
  od;
  return [w, e];
end;

# Abstract Stabilizer Chains
# ==========================

# Methoden
#   * Orbit-Expansion: 
#       + Inkrementell: Optimiert immer das ganze Orbit; deshalb geht
#         viel weniger durch die Lappen
#       + ber"ucksichtigt die Inverse gleich mit: Abstand ist Metrik
#       + managed eine Agenda: Eliminiert viele redundante Tests
#       + Einf"ugen (insert) und Agenda leeren (flush) sind getrennt:
#         bessere Kontrolle der Rechenzeit
#       + Flush testet ob das Orbit voll ist (konkrete StabChain n"otig)
#       + Flush managed eine Maximall"ange wenn das Orbit voll ist:
#         viele erfolglose Versuche werden fr"uher abgebrochen
#
#   * Quotientenbildung: 
#       + managed eine Kandidatenliste f"ur jeden Basisbildpunkt:
#         Es m"ussen nur Sum(Binomial(|Kandidaten[i]|, 2), i in Orbit)
#         statt Binomial(Sum(|Kandidaten[i]|, i in Orbit), 2) viele
#         Quotienten gebildet werden.
#     [+] betrachtet entweder x/y oder y/x = (x/y)^-1: Orbit-Expansion
#         ber"ucksichtigt die Inverse automatisch mit
#     [+] merkt sich welche Quotienten schon verbraucht wurden
#     [+] kann auch r"uckw"arts verwendet werden: Zu einer gegebenen
#         L"ucke im Orbit des Stabilisators kann schnell der k"urzeste 
#         Quotient aus einem Level dar"uber gefunden werden, der die
#         L"ucke stopft (falls sowas existiert).
#
#   * Schreiertripel-Bildung:
#     [+] managed ein kleines, kurzes Erzeugendensystem auf jedem
#         Level: f"ullt deterministisch den Stabilisator (Huppi, I.1.19.10)
#     [+] merkt sich welche Tripel schon verbraucht wurden
#      -  Bug: Ihm scheint etwas durch die Lappen zu gehen.
#
#   * Einf"ugen der k"urzesten Elemente:
#     [+] entfernt die Inversen: Orbit-Expansion ber"ucksichtigt diese wieder
#
#   * Einf"ugen von konjugierten faulsten Elementen:
#     [+] versucht die Qualit"at eines Elements zu extrapolieren und
#         konjugiert es dann unterschiedlich viel: Reduziert Komplexit"at
#     [+] die Menge der konjugierenden Elemente wird partitioniert bzgl.
#         des Urbilds des Basispunkts (x^y in G_b <==> b/y Fixp. von x).
#     [+] die Menge der lazy Elemente wird verkleinert auf die, die es
#         "uberhaupt bis in den dritten Stabilisator schaffen (Reduktion).
#     [+] Ziehen von zuf"alligen faulen Elementen bringt auch etwas.
#
#   * Rekursives Einf"ugen (von zuf"alligen Elementen):
#     [+] betrachtet sowohl x/T[b^x] als auch T[b/x]*x (falls diese nicht
#         direkt oder durch Inversion aus einander hervorgehen)
#     [+] managed L"angenschranken f"ur die einzelnen Level: erfolglose
#         Versuche werden fr"uh abgebrochen
#
#   * Gute Basis w"ahlen:
#      + 'Tiefstopf-Methode'
#
#   * Gute Erzeuger w"ahlen:
#     [?] Vielleicht lohnt es sich, statt G = <x, y> die Gruppe durch
#         G = <x, z> mit y = x^z zu erzeugen. Das darf man machen, obwohl
#         man f"ur z eigentlich kein Wort in {x, y} kennt (bzw. nur lange)
#         weil y = x^z <==> z y = x z, d.h. durch Vorbeischieben kann man
#         immer z eliminieren und y wieder hineinbringen (am Ende).

# G.abstractStabilizerChain
#   base[level]                                    basepoint of level
#   transversals[level][basepointImage][candidate] is [word, perm]-pair
#   orbits[level]                                  set of basepoint images
#   orbitGraphs[level]                             
#     basepoint                                    = base[level]
#     points                                       >= orbits[level]
#     word[point1][point2] (where point1 > point2) mapping word 1 -> 2  
#     agenda                                       set of [p, q]-pairs recently updated
#     agendaFlush                                  high water mark to flush agenda

ASCOps := rec( );

ASCOps.Print := function ( A )
  local level, T, format, avgLength, sum, nr, num, den;

  format := function (width, x)
    x := String(x);
    while LengthString(x) < width do
      x := ConcatenationString(" ", x);
    od;
    return x;
  end;

  T := [ ];
  for level in [1..Length(A.base)] do
    ASCOps.FlushSchreier(A.group, level);

    # switch of redundant Schreier-structures
    if 
      false and # ...ist nicht unbedingt gut
      level > 1 and A.schreiers[level].isComplete and 
      A.schreiers[level-1].isComplete 
    then
      A.schreiers[level-1].isEnabled := false;
    fi;

    ASCOps.FlushOrbitGraph(A.group, level);
    Add(T, ASCOps.TransversalOrbitGraph(A.group, level));
  od;

  Print(
    "ASC(\n",
    "# level basepoint cosets  (orbit size) (max. length) (avg. length)\n"
  );
  for level in [1..Length(A.base)] do
    if not IsBound(A.orbits) or Length(A.orbits[level]) > 1 then
      Print(
        "# ", 
        format(5, level), " ", 
        format(9, A.base[level]), " "
      );
      if IsBound(A.orbits) then
        Print(format(6, Length(A.orbits[level])), "  ");
      else
        Print(format(6, "unknown"), "  ");
      fi;
      Print(format(11, Number(T[level])));
      if IsBound(A.orbits) and Number(T[level]) = Length(A.orbits[level]) then
        if A.schreiers[level].isComplete then
          Print("* ");
        else
          Print("+ ");
        fi;
      else
        Print("  ");
      fi;
      sum := Sum(ListSqueezed(T[level], x -> LengthWord(x[1])));
      nr  := Number(T[level]);
      Print( 
        format(
          13, 
          Maximum(ListSqueezed(T[level], x -> LengthWord(x[1])))
        ), 
        " ",
        format(      # eine Nachkommastelle
          13, 
          ConcatenationString(
            String(QuoInt(sum,nr)),
            ".",
            String(QuoInt(10*sum, nr) mod 10)
          )
        ),
        "\n"
      );
    fi;
  od;
  Print("#\n# total:          ");
  if IsBound(A.orbits) then
    Print(format(6, Sum(List(A.orbits, Length))), "  ");
  else
    Print(format(6, "unknown"), "  ");
  fi;
  avgLength := 0;
  for level in [1..Length(A.base)] do
    avgLength := 
      avgLength + 
      Sum(ListSqueezed(T[level], x -> LengthWord(x[1]))) / Number(T[level]);
  od;
  Print(format(11, Sum(List(T, Number))));
  if IsBound(A.orbits) and Sum(List(T, Number)) = Sum(List(A.orbits, Length)) then
    Print("* ");
  else
    Print("  ");
  fi;
  num := Numerator(avgLength);
  den := Denominator(avgLength);
  Print(
    format(
      13, 
      Sum( 
        List(
          T, 
          Tlevel -> Maximum(ListSqueezed(Tlevel, x -> LengthWord(x[1])))
        ) 
      )
    ), " ",
    format(
      13, 
      ConcatenationString(
        String(QuoInt(num, den)),
        ".",
        String(QuoInt(10*num, den) mod 10)
      )
    ), 
    "\n"
  );
  Print("#    (orbits: + = complete, * = generating set known)\n)\n");
end;

# Incremental orbit expansion
# ===========================

# Lemma:
#   G = (V, V x V, w) sei ein ungerichteter vollst"andiger bewerteter Graph.
#   Die Bewertung w ist genau dann eine Metrik, wenn sie positiv definit ist
#   und in jedem Dreieck gilt die Dreiecksungleichung.
# Bew.-Idee:
#   Betrachte ein minimales Gegenbeispiel (Weg der L"ange > 3) mit einer
#   zu langen Kante). Dann kann der Weg verk"urzt werden und war also 
#   nicht minimal. 

# Schranken f"ur die Wortl"ange eines Kandidaten wenn das Orbit voll ist:
#   Angenommen wir vernachl"assigen den Effekt, da"s zuf"allige 
#   Wortverk"urzungen durch (..g) * (g^-1..) auftreten k"onnen.
#     Ein Kandidat x soll direkt oder indirekt zu einer Verk"urzung
#   der Transversalenelemente w[1], .., w[n-1] f"uhren. 
#   Durch die Dreiecksungleichung sieht man
#     a) direkt:   Nur m"oglich bei x < max_i w[i].
#     b) indirekt: Nur m"oglich bei x + min_i w[i] < max_i w[i].
#   Allerdings kann es sein, da"s x zwar nicht zu einer Verbesserung
#   eines Transversalenelements f"uhrt, sich aber in dem Augenblick
#   nutzen l"a"st wo ein Transversalenelement schrumpft.

# create orbit graph
ASCOps.NewOrbitGraph := function ( G, level )
  local A, points, basepoint, orbgraph, p;

  A := G.abstractStabChain;
  points := A.orbits[level];
  basepoint := A.base[level];

  orbgraph := rec(level := level);

  orbgraph.points    := Set(points);
  orbgraph.basepoint := basepoint;

  # p^word[p][q] = q 
  orbgraph.word := [ ];
  for p in points do
    orbgraph.word[p] := [ ];
  od;

  # list of [p, q] where p > q of edges recently modified
  orbgraph.agenda := [ ];

  # How often to flush the agenda? There are Binomial(|points|, 2) many
  # possible positions in word[p][q] (p > q); if 10% of them has been 
  # updated then we force flushing the agenda (may be expensive).
  orbgraph.agendaFlush := QuoInt(Binomial(Length(orbgraph.points), 2), 10);

# ...flush praktisch abgestellt
  orbgraph.agendaFlush := Binomial(Length(orbgraph.points), 2);

  if orbgraph.agendaFlush = 0 then
    orbgraph.agendaFlush := 1;
  fi;

  # Is the orbit complete? (Updated in flush)  
  orbgraph.isComplete := false;

  return orbgraph;
end;

# flush orbgraph.agenda
ASCOps.FlushOrbitGraph := function ( G, level ) 
  local orbgraph, w, p, q, r, w_p, w_p_q, update, b, len;

  orbgraph := G.abstractStabChain.orbitGraphs[level];
  if Length(orbgraph.agenda) = 0 then
    return;
  fi;
  InfoASC1("#I flushing agenda of orbit graph on level ", orbgraph.level, "\n");

  # procedure to update and add to agenda
  update := function (p, q, word)
    w[p][q] := word;
    AddSet(orbgraph.agenda, [p, q]);
  end;

  # update until the situation stabilizes
  w := orbgraph.word;
  while IsBound(orbgraph.agenda[1]) do

    # get p -> q (where p > q) as first item of agenda
    p     := orbgraph.agenda[Length(orbgraph.agenda)][1];
    q     := orbgraph.agenda[Length(orbgraph.agenda)][2];
    w_p_q := w[p][q];
    Unbind(orbgraph.agenda[Length(orbgraph.agenda)]);

    # update triangles pqr (p -> q has beed shortened)
    for r in orbgraph.points do

      # switch on order of points (w[x][y] needs x > y)
      if q > r then # p > q > r

        if IsBound(w[p][r]) then
          if IsBound(w[q][r]) then
            if w_p_q * w[q][r] < w[p][r] then # ...time critical: allocating useless words
              update(p, r, w_p_q * w[q][r]);
            elif LeftQuotient(w_p_q, w[p][r]) < w[q][r] then
              update(q, r, LeftQuotient(w_p_q, w[p][r]));
            fi;
          else
            update(q, r, LeftQuotient(w_p_q, w[p][r]));
          fi;
        elif IsBound(w[q][r]) then
          update(p, r, w_p_q * w[q][r]);
        fi;

      elif p > r and r > q then

        if IsBound(w[p][r]) then
          if IsBound(w[r][q]) then
            if w_p_q / w[r][q] < w[p][r] then
              update(p, r, w_p_q / w[r][q]);
            elif LeftQuotient(w[p][r], w_p_q) < w[r][q] then
              update(r, q, LeftQuotient(w[p][r], w_p_q));
            fi;
          else
            update(r, q, LeftQuotient(w[p][r], w_p_q));
          fi;
        elif IsBound(w[r][q]) then
          update(p, r, w_p_q / w[r][q]);
        fi;

      elif r > p then # r > p > q

        if IsBound(w[r][p]) then
          if IsBound(w[r][q]) then
            if w[r][q] / w_p_q < w[r][p] then
              update(r, p, w[r][q] / w_p_q);
            elif w[r][p] * w_p_q < w[r][q] then
              update(r, q, w[r][p] * w_p_q);
            fi;
          else
            update(r, q, w[r][p] * w_p_q);
          fi;
        elif IsBound(w[r][q]) then
          update(r, p, w[r][q] / w_p_q);
        fi;

      fi;
    od;
  od;

  # check if the orbit is complete (= |points| many points reachable)
  if not orbgraph.isComplete then
    orbgraph.isComplete := 
      Number( w[ Maximum(orbgraph.points) ] ) + 1 = 
      Length(orbgraph.points);
    if orbgraph.isComplete then
      InfoASC1("#I level ", orbgraph.level, " is complete\n");
    fi;
  fi;

  # compute upper bounds on direct/indirect replacements
  if orbgraph.isComplete then

    # max length of a word
    orbgraph.max := 0;
    for w_p in orbgraph.word do
      for w_p_q in w_p do
        if LengthWord(w_p_q) > orbgraph.max then
          orbgraph.max := LengthWord(w_p_q);
        fi;
      od;
    od;

    # max/min length of non-trivial transversal element

    orbgraph.maxTransversal := 0;
    orbgraph.minTransversal := orbgraph.max;

    b := orbgraph.basepoint;
    for p in orbgraph.points do
      if p <> b then
        if p > b and IsBound(w[p][b]) then
          len := LengthWord(w[p][b]);
      orbgraph.maxTransversal := 
        Maximum(orbgraph.maxTransversal, len);
      orbgraph.minTransversal := 
        Minimum(orbgraph.minTransversal, len);
        elif p < b and IsBound(w[b][p]) then
          len := LengthWord(w[b][p]);
      orbgraph.maxTransversal := 
        Maximum(orbgraph.maxTransversal, len);
      orbgraph.minTransversal := 
        Minimum(orbgraph.minTransversal, len);
        fi;
      fi;
    od;
  fi;
end;

# insert [word, perm] into orbgraph
ASCOps.InsertOrbitGraph := function ( G, level, word, perm )
  local
    orbgraph,
    p, q,    # points
    w,       # = orbgraph.word
    wordInv, # = word^-1
    update;  # procedure to update p -> q with word

  # shortcuts
  orbgraph := G.abstractStabChain.orbitGraphs[level];
  if 
    perm = () or
    orbgraph.isComplete and LengthWord(word) > orbgraph.max 
  then
    return;
  fi;

  # fetch constants
  w       := orbgraph.word;
  wordInv := word^-1;

  # update and add to agenda; agenda contains [p, q]-pairs (where p > q)
  # of edges which have been updated recently
  update := function (p, q, word)
    w[p][q] := word;
    AddSet(orbgraph.agenda, [p, q]);
  end;

  # augment agenda using [word, perm]
  for p in orbgraph.points do
    q := p^perm;
    if   p > q and ( not IsBound(w[p][q]) or word    < w[p][q] ) then
      update(p, q, word);
    elif p < q and ( not IsBound(w[q][p]) or wordInv < w[q][p] ) then
      update(q, p, wordInv);
    fi;
  od;

  if Length(orbgraph.agenda) >= orbgraph.agendaFlush then
    ASCOps.FlushOrbitGraph(G, level);
  fi;  
end;

# extract transversal from orbgraph
ASCOps.TransversalOrbitGraph := function ( G, level )
  local orbgraph, T, b, p;

  ASCOps.FlushOrbitGraph(G, level);
  orbgraph := G.abstractStabChain.orbitGraphs[level];

  T    := [ ];
  b    := orbgraph.basepoint;
  T[b] := IdWord;
  for p in orbgraph.points do
    if   p < b and IsBound(orbgraph.word[b][p]) then
      T[p] := orbgraph.word[b][p];
    elif p > b and IsBound(orbgraph.word[p][b]) then
      T[p] := orbgraph.word[p][b]^-1;
    fi;
    if IsBound(T[p]) then
      T[p] := [ T[p], MappedWord(T[p], G.abstractGenerators, G.generators) ];
    fi;
  od;
  return T;
end;

# Producing quotients
# ===================

# create new generator of quotients
ASCOps.NewQuotients := function ( G, level )
  local A, points, basepoint, quots, p;

  A := G.abstractStabChain;
  points := A.orbits[level];
  basepoint := A.base[level];

  quots :=
    rec(
      level         := level,
      maxWordLength := "infinity", # bound on quotients produced
      maxCandidates := 100,
      points        := points,
      basepoint     := basepoint,
      new           := [ ],
      used          := [ ],
      quotients     := [ ]
    );
  for p in quots.points do
    quots.new[p]  := [ ];
    quots.used[p] := [ ];
  od;
  return quots;
end;

# add [word, perm] to list of raw material
ASCOps.InsertQuotients := function ( G, level, word, perm )
  local quots, p, i;

  quots := G.abstractStabChain.quotients[level];
  if LengthWord(word) > quots.maxWordLength then
    return;
  fi;
  p := quots.basepoint^perm;
  if p = quots.basepoint then
    return;
  fi;

  i := PositionProperty(quots.new[p], x -> x[2] = perm);
  if i = false then
    Add(quots.new[p], [ word, perm ]);
  else
    if word < quots.new[p][i] then
      quots.new[p][i][1] := word;
    fi;
  fi;
  if Length(quots.new[p]) = quots.maxCandidates + 1 then
    Sort(quots.new[p]);
    Unbind(quots.new[p][Length(quots.new[p])]);
  fi;
end;

nrQuotientNews := function ( G )
  local A, quots, sum, level, p;

  A     := G.abstractStabChain;
  quots := G.abstractStabChain.quotients;
  sum   := 0;
  for level in [1..Length(A.base)] do
    for p in [1..Length(quots[level].new)] do
      if IsBound(quots[level].new[p]) then
        sum := sum + Length(quots[level].new[p]);
      fi;
    od;
  od;
  return sum;
end;


# fill quots.quotients with new quotients
ASCOps.FlushQuotients := function ( G, level ) 
  local quots, N, U, p, n, Npn1, Npn2, Upu, q;

  quots := G.abstractStabChain.quotients[level];
  if ForAll(quots.points, p -> Length(quots.new[p]) <= 1) then
    return;
  fi;
  InfoASC1("#I computing quotients on level ", quots.level, "\n");

  N := quots.new;
  U := quots.used;
  for p in quots.points do
    if Length(U[p]) = 0 and Length(N[p]) >= 1 then

      # move last(N[p]) to U[p]
      n := Length(N[p]);
      Add(U[p], N[p][n]);
      Unbind(N[p][n]);
    fi;
    if Length(U[p]) >= 1 and Length(N[p]) >= 1 then

      # add quotients U[p][u]/N[p][n] for all u, n
      n := Length(N[p]);
      repeat

        # add quotients U[p][u]/N[p][n] for all u
        Npn1 := N[p][n][1];
        Npn2 := N[p][n][2];
        for Upu in U[p] do
          q := [ Upu[1]/Npn1, Upu[2]/Npn2 ];
          if LengthWord(q[1]) <= quots.maxWordLength then
            Add(quots.quotients, q);
          fi;
        od;

        # move N[p][n] from N[p] to U[p]
        Add(U[p], N[p][n]);
        Unbind(N[p][n]);
        n := n - 1;

      until n = 0;
    fi;
    Sort(U[p]);
    while Length(U[p]) > quots.maxCandidates do
      Unbind(U[p][Length(U[p])]);
    od;
  od;
end;

# reduce the maximal admissable word length of quotients
ASCOps.ReduceMaxWordLength := function ( quots, maxWordLength )
  local p;

  # remove elements larger than maxWordLength
  quots.maxWordLength := maxWordLength;
  quots.quotients := 
    Filtered(quots.quotients, x -> LengthWord(x[1]) <= maxWordLength);
  for p in quots.points do
    quots.new[p]  := 
      Filtered(quots.new[p],  x -> LengthWord(x[1]) <= maxWordLength-1);
    quots.used[p] := 
      Filtered(quots.used[p], x -> LengthWord(x[1]) <= maxWordLength-1);
  od;
end;

ASCOps.QuotientPairs := function ( G, level )
  local quots, Q;

  ASCOps.FlushQuotients(G, level);
  quots := G.abstractStabChain.quotients[level];
  Q := quots.quotients;
  quots.quotients := [ ];

  return Set(Q);
end;

# Producing Schreier-triples
# ==========================

ASCOps.NewSchreier := function ( G, level )
  local schr, A;

  A := G.abstractStabChain;

  schr := rec( );

  schr.level         := level;
  schr.maxGenerators := 1000; # when to reduce generators again
  schr.group         := Stabilizer(G, Sublist(A.base, [1..level-1]), OnTuples);
  schr.generators    := Set([ ]);
  schr.generatorSpan := Subgroup(schr.group, [ ]);
  schr.isReduced     := true;
  schr.isComplete    := false;
  schr.isEnabled     := true; # switch off if level+1 is complete

  return schr;
end;

# reduziere schr.generators um redundante Erzeuger
ASCOps.FlushSchreier := function ( G, level ) 
  local schr, S, x;

  schr := G.abstractStabChain.schreiers[level];
  if schr.isReduced then
    return;
  fi;
  InfoASC1("#I filtering generating set of level ", schr.level, "\n");
  S                  := Set(schr.generators);
  schr.generators    := Set([ ]);
  schr.generatorSpan := Subgroup(schr.group, [ ]);
  for x in S do
    if not x[2] in schr.generatorSpan then
      AddSet(schr.generators, x);
      schr.generatorSpan := Closure(schr.generatorSpan, x[2]);
    fi;
  od;
  schr.isComplete := Size(schr.generatorSpan) = Size(schr.group);
  schr.isReduced  := true;
end;

ASCOps.SchreierGeneratingSet := function ( G, level )
  local schr;

  schr := G.abstractStabChain.schreiers[level];
  if not schr.isComplete then
    return false;
  fi;
  ASCOps.FlushSchreier(G, level);
  return schr.generators;
end;

# neuer potentieller Erzeuger [word, perm]
ASCOps.InsertSchreier := function ( G, level, word, perm )
  local schr;

 return; # neuer Ansatz...

  schr := G.abstractStabChain.schreiers[level];
  if not schr.isEnabled then
    return;
  fi;
  if schr.isComplete or perm in schr.generatorSpan then

    # add [word, perm] if it is shorter
    if word >= schr.generators[Length(schr.generators)][1] then
      return;
    fi;
    AddSet(schr.generators, [word, perm]);
    schr.isReduced := false;
    if Length(schr.generators) > schr.maxGenerators then
      ASCOps.FlushSchreier(G, level);
    fi;
    return;

  else # not complete

    # add [word, perm] and compute closure again
    AddSet(schr.generators, [ word, perm ]);
    schr.generatorSpan := Closure(schr.generatorSpan, perm);
    if Size(schr.generatorSpan) = Size(schr.group) then
      InfoASC1("#I generating set known for level ", schr.level, "\n");
      schr.isComplete := true;

# schalte dar"uber und darunter aus falls m"oglich...

    fi;
    return;
  fi;
end;

ASCOps.SchreierPairs := function ( G, level )
  local A, schr, S, T, b, Q, Q1, v, u, s, us, vInv, usv, p;

# neuer Ansatz...
# A := G.abstractStabChain;
# T := []; for p in [level..Length(A.base)] do 
# Append(T, List(ASCOps.TransversalOrbitGraph(G, p), x -> x)); od;
# A.schreiers[level].generators := T;
# A.schreiers[level].isReduced  := false;
# ASCOps.FlushSchreier(G, level);

 
  # fetch generating set S
  A    := G.abstractStabChain;
  schr := A.schreiers[level];
  S    := ASCOps.SchreierGeneratingSet(G, level);
  if S = false then
    return [ ];
  fi;

  # fetch transversal
  b := A.base[level];
  T := ASCOps.TransversalOrbitGraph(G, level);

  # form all Schreier-triples
  Q := [ ];
  for u in T do
    for s in S do
      us   := [ u[1]*s[1], u[2]*s[2] ];
      if IsBound(T[ b^us[2] ]) then
        vInv := T[ b^us[2] ];
        usv  := [ us[1]/vInv[1], us[2]/vInv[2] ];
        Add(Q, usv);
      fi;
    od;
  od;
  if Length(Q) = 0 then
    return Q;
  fi;

  # remove duplicated permutations
  Q := List(Q, Reversed);
  Sort(Q);
  Q1 := [ ];
  u  := Q[1];
  for v in Q do
    if v[1] <> u[1] then
      Add(Q1, Reversed(u));
      u := v;
    fi;
  od;
  Add(Q1, Reversed(u));
  Sort(Q1);
  return Q1;
end;


# Inserting [word, perm]-pairs
# ============================

ASCOps.Insert1A := function ( G, word, perm ) 
  local A, level, base, T, Tp, p, k;

  if perm = () then
    return [0, 0];
  fi;

  # get level; level <= Length(base) since only perm = () stabilizes more
  A     := G.abstractStabChain;
  level := 1;
  base  := A.base;
  while base[level]^perm = base[level] do
    level := level + 1;
  od;
  ASCOps.InsertOrbitGraph(G, level, word, perm);
  ASCOps.InsertSchreier(G, level, word, perm);
  ASCOps.InsertQuotients(G, level, word, perm);
  return [0, 0];
end;

# returns [top-replacements, replacements]
ASCOps.Insert1 := function ( G, word, perm ) 
  local A, level, base, T, Tp, p, k;

  if perm = () then
    return [0, 0];
  fi;

  # get level; level <= Length(base) since only perm = () stabilizes more
  A     := G.abstractStabChain;
  level := 1;
  base  := A.base;
  while base[level]^perm = base[level] do
    ASCOps.InsertOrbitGraph(G, level, word, perm);
    ASCOps.InsertSchreier(G, level, word, perm);
    level := level + 1;
  od;
  ASCOps.InsertOrbitGraph(G, level, word, perm);
  ASCOps.InsertSchreier(G, level, word, perm);
  ASCOps.InsertQuotients(G, level, word, perm);
  return [0, 0];
end;

ASCOps.InsertA := function ( arg )
  local pairs, sum;

  if Length(arg) = 3 then
    return ASCOps.Insert1A(arg[1], arg[2], arg[3]);
  elif Length(arg) = 2 and IsWord(arg[2]) then
    return 
      ASCOps.Insert1A(
        arg[1], 
        arg[2], 
        MappedWord(arg[2], arg[1].abstractGenerators, arg[1].generators)
      );
  elif Length(arg) = 2 and IsWord(arg[2][1]) and IsPerm(arg[2][2]) then
    return ASCOps.Insert1A(arg[1], arg[2][1], arg[2][2]);
  else
    sum := ASCOps.Insert1A(arg[1], IdWord, ());
    for pairs in arg[2] do
      sum := sum + ASCOps.InsertA(arg[1], pairs);
    od; 
    return sum;
  fi;
end;

ASCOps.Insert := function ( arg )
  local pairs, sum;

  if Length(arg) = 3 then
    return ASCOps.Insert1(arg[1], arg[2], arg[3]);
  elif Length(arg) = 2 and IsWord(arg[2]) then
    return 
      ASCOps.Insert1(
        arg[1], 
        arg[2], 
        MappedWord(arg[2], arg[1].abstractGenerators, arg[1].generators)
      );
  elif Length(arg) = 2 and IsWord(arg[2][1]) and IsPerm(arg[2][2]) then
    return ASCOps.Insert1(arg[1], arg[2][1], arg[2][2]);
  else
    sum := ASCOps.Insert1(arg[1], IdWord, ());
    for pairs in arg[2] do
      sum := sum + ASCOps.Insert(arg[1], pairs);
    od; 
    return sum;
  fi;
end;

ASCOps.InsertRecursive := function (G, pair)
  local A, T, level, level1, b, s, p, word, perm;

  word := pair[1];
  perm := pair[2];
  A := G.abstractStabChain;

  T := [ ];
  for level in [1..Length(A.base)] do
    Add(T, ASCOps.TransversalOrbitGraph(G, level));
  od;
 
  s := ASCOps.Insert1(G, IdWord, ());
  s := s + ASCOps.Insert1(G, word, perm);
  for level in [1..Length(A.base)] do
    b    := A.base[level];
    if not IsBound(T[level][b^perm]) then
      T := [ ];
      for level1 in [1..Length(A.base)] do
    Add(T, ASCOps.TransversalOrbitGraph(G, level1));
      od;
    fi;
    word := word / T[level][b^perm][1];
    perm := perm / T[level][b^perm][2];
    s := s + ASCOps.Insert1(G, word, perm);
    if LengthWord(word) > 20 then
      return s;
    fi;
    if perm = () then
      return s;
    fi;
#Print(LengthWord(word), " \c");
  od;
  return s;
end;


ASCOps.InsertCollisionPairs1 := function ( G, level ) #...alt
  local useful, T, we1, we2;

  InfoASC1("#I useful collisions of level ", level, ": \c");
  useful := 0;
  for T in G.abstractStabChain.transversals[level] do
    for we1 in T do
      for we2 in T do
        useful := useful + ASCOps.Insert1(G,  we1[1]/we2[1], we1[2]/we2[2]);
      od;
    od;
  od;
  InfoASC1(useful, "\n");
  return useful;
end;

ASCOps.InsertCollisionPairs := function ( G, level)
  local x, useful;
  
  ASCOps.FlushQuotients(G, level);
  useful := ASCOps.Insert1(G, IdWord, ());
  for x in G.abstractStabChain.quotients[level].quotients do
    useful := useful + ASCOps.Insert1(G, x[1], x[2]);
  od;
  G.abstractStabChain.quotients[level].quotients := [ ];
  return useful;
end;


ASCOps.InsertConjugatedPairs := function ( G, lazyPairs, conjugatingPairs )
  local we1, we2, s;

  s := ASCOps.Insert1(G, IdWord, ());
  for we1 in lazyPairs do
    for we2 in conjugatingPairs do
      s := s + ASCOps.Insert1(G, we1[1]^we2[1], we1[2]^we2[2]);
    od;
  od;
  return s;
end;


ASCOps.ComputeOrbits := function ( G )
  local base, S, level;

  base := G.abstractStabChain.base;
  MakeStabChain(G, base);
  ExtendStabChain(G, base);
  S := G; # ... G.stabChain;
  G.abstractStabChain.orbits := [ ];
  for level in [1..Length(base)] do
    Add(G.abstractStabChain.orbits, Set(S.orbit));
    S := S.stabilizer;
  od;
end;

ASCOps.New := function ( G, maxLengthTransversal, initialBaseSegment )
  local m, sp, base, T, level, reduce, A;

  base := HeuristicBase(G, initialBaseSegment);

  G.abstractStabChain := 
    rec(
      group                := G,
      base                 := base,
      maxLengthTransversal := maxLengthTransversal,
      transversals         := [ ],
      orbitGraphs          := [ ],
      quotients            := [ ],
      schreiers            := [ ],
      operations           := ShallowCopy( ASCOps )
    );
  A := G.abstractStabChain;

  ASCOps.ComputeOrbits(G);

  # reduce base
  reduce   := Filtered([1..Length(A.base)], i -> Length(A.orbits[i]) > 1);
  A.base   := Sublist(A.base,   reduce);
  A.orbits := Sublist(A.orbits, reduce);

  # set transversals
  T := A.transversals;
  for level in [1..Length(A.base)] do
    T[level]                := [ ];
    T[level][A.base[level]] := Set([ [IdWord, ()] ]);
  od;

  # initialize orbit graphs, quotients, Schreier sets
  for level in [1..Length(A.base)] do
    A.orbitGraphs[level] := ASCOps.NewOrbitGraph(G, level);
    A.quotients[level]   := ASCOps.NewQuotients(G, level);
    A.schreiers[level]   := ASCOps.NewSchreier(G, level);
  od;
end;

ASCOps.StrongGenerators := function ( G )
  local A, S, S1, s, level, T;

  A := G.abstractStabChain;
  S := [ ];
  for level in [1..Length(A.base)] do

    # add a transversal of this level
    T := ASCOps.TransversalOrbitGraph(G, level);
    UniteSet(S, List(Filtered(T, x -> x[2] <> ()), x -> x[1]));
  od;

  # remove redundant inverses
  S1 := [ ];
  for s in S do
    if not s^-1 in S1 then
      AddSet(S1, s);
    fi;
  od;

  return S1;
end;

# Beispiel1
# =========

# Kugelbrezel, SE, 11.4.96, GAP v3.1
#
#                 35 36 37 38   1  2  3  4
#               34           20            5 
#             33           19  21    ---     6
#             32           18  22   |   |    7
#             31           17  23   |   |    8
#             30           16  24    ---     9
#               29           15           10
#                 28 27 26 25  14 13 12 11

#                  h  u  l  a   c  r  q  b
#                f            a            n 
#              j            a   g    ---     w
#              v            p   t   |   |    w
#              v            r   l   |   |    w
#              k            c   a    ---     w
#                e            a            s
#                  d  m  t  g   a  o  r  i

if false and not IsBound(G) then

sR := ( 1, 2, 3, 4, 5, 6, 7, 8, 9,10,11,12,13,14,15,16,17,18,19,20);
R  := AbstractGenerator("R");
sL := (20,21,22,23,24,15,25,26,27,28,29,30,31,32,33,34,35,36,37,38); 
L  := AbstractGenerator("L");
G  := Group(sL, sR); G.abstractGenerators := [L, R];

EnumeratePermGroup(G);

ASCOps.New(G, 10, []);
ASCOps.ComputeOrbits(G);
A := G.abstractStabChain;
Print("A = ", A, "\n");

fi; # G

# Beispiel2
# =========

if false and not IsBound(G) then

# Rubik's 3x3x3-cube
#
#                          +--------------+
#                          |  1    2    3 |
#                          |  4  top    5 |
#                          |  6    7    8 |
#           +--------------+--------------+--------------+--------------+
#           |  9   10   11 | 17   18   19 | 25   26   27 | 33   34   35 |
#           | 12  left  13 | 20 front  21 | 28 right  29 | 36  rear  37 |
#           | 14   15   16 | 22   23   24 | 30   31   32 | 38   39   40 |
#           +--------------+--------------+--------------+--------------+
#                          | 41   42   43 |
#                          | 44 bottom 45 |
#                          | 46   47   48 |
#                          +--------------+
G := Group(
  ( 1, 3, 8, 6)( 2, 5, 7, 4)( 9,33,25,17)(10,34,26,18)(11,35,27,19),
  ( 9,11,16,14)(10,13,15,12)( 1,17,41,40)( 4,20,44,37)( 6,22,46,35),
  (17,19,24,22)(18,21,23,20)( 6,25,43,16)( 7,28,42,13)( 8,30,41,11),
  (25,27,32,30)(26,29,31,28)( 3,38,43,19)( 5,36,45,21)( 8,33,48,24),
  (33,35,40,38)(34,37,39,36)( 3, 9,46,32)( 2,12,47,29)( 1,14,48,27),
  (41,43,48,46)(42,45,47,44)(14,22,30,38)(15,23,31,39)(16,24,32,40)
);

EnumeratePermGroup(G);

ASCOps.New(G, 10, []);
# ASCOps.ComputeOrbits(G);
A := G.abstractStabChain;
Print("A = ", A, "\n");

# 1. InsertConjugatedPairs(20, shortPairs)
# 2. total riesel von unten hoch
# 3. orbit expand auf allen leveln
# 4. riesel wo's noch klemmt
# 5. orbit expand ebendort
# 6. Alle Kandidaten aus Stabilisatoren tiefer als das erste Orbit
#    mit wenigen (ca. 10) Zufallselementen aus shortPairs konjugieren.
# --> sum max. Length = 194; sum avg. Length = 114

# Mit AbStab.g
# ------------

# orbit  max avg
# [ 24,   4, 13/6 ], 
# [ 22,   5, 71/22 ], 
# [ 20,   6, 16/5 ], 
# [ 18,   7, 35/9 ], 
# [ 16,  11, 51/8 ], 
# [ 14,   9, 11/2 ], 
# [ 12,  13, 13/2 ], 
# [ 10,   8, 53/10 ], 
# [  8,  14, 15/2 ], 
# [  6,  20, 32/3 ], 
# [  4,  27, 14 ], 
# [ 24, 100, 158/3 ], 
# [ 21,  86, 332/7 ], 
# [ 18, 118, 623/9 ], 
# [ 15, 238, 636/5 ], 
# [ 12, 530, 1571/6 ], 
# [  9, 564, 376 ], 
# [  3, 644, 1288/3 ]
#
# total: orbits = 256, sum max = 2404, sum avg = 1432

# Short-Pairs bis L"ange 3 (incl.) und dann nur Schreier
# ------------------------------------------------------
#
# level basepoint cosets  (orbit size) (max. length) (avg. length)
#     1         2     24           24*             4             2
#     2         4     22           22*             5             2
#     3         5     20           20*             5             2
#     4         7     18           18*             5             3
#     5        12     16           16*             7             4
#     6        13     14           14*             7             4
#     7        15     12           12*             7             3
#     8        21     10           10*            22            14
#     9        23      8            8*            19            10
#    10        29      6            6*            32            20
#    11        31      4            4*            49            25
#    12         1     24           24*            86            51
#    13         3     21           21*            64            53
#    14         6     18           18*            42            28
#    15         8     15           15*            84            47
#    16        14     12           12*           140            86
#    17        16      9            9*           250           137
#    18        24      3            3*           234           156
#
# total:             256          256*          1062           653
#    (orbits: + = complete, * = generating set known)
# )
 
# Tiefstopf-Basis aus den Lazy-Pairs mit 12k shortPairs; nur Schreier
# -------------------------------------------------------------------
#
# level basepoint cosets  (orbit size) (max. length) (avg. length)
#     1        48     24           24*             3             1
#     2        43     21           21*             4             2
#     3        41     18           18*             4             2
#     4        42     24           24*            16             9
#     5        45     22           22*            16             9
#     6        36     20           20*             9             5
#     7        28     18           18*            12             6
#     8        20     16           16*             9             5
#     9        47     14           14*             8             4
#    10        44     12           12*             8             4
#    11        26     10           10*             7             3
#    12        34      8            8*             8             4
#    13        33     15           15*            14             9
#    14        37      6            6*             8             4
#    15        18      4            4*            26            15
#    16        46     12           12*            66            44
#    17        35      9            9*           124            84
#    18        25      3            3*            94            62
#
# total:             256          256*           436           283
#    (orbits: + = complete, * = generating set known)

# ins  := x -> ASCOps.Insert(G, x);
# insR := x -> ASCOps.InsertRecursive(G, x);
# rie  := i -> ASCOps.InsertCollisionPairs(G, i);
# sch  := i -> ASCOps.InsertSchreierPairs(G, i);
# con  := x -> ASCOps.InsertConjugatedPairs(G, x, G.shortPairs);

fi; # G

# Experimente...
# ==============

ways := function (G, pairs)
  local counts, A, level, xx, x, p;

  ASCOps.ComputeOrbits(G);
  A := G.abstractStabChain;
  counts := List(A.base, p -> List([1..Length(A.base)], i -> 0));
  for xx in pairs do
    x := xx[2];
    for level in [1..Length(A.base)] do
      p                := A.base[level]^x;
      x                := x / A.transversals[level][p][1][2];
      counts[level][p] := counts[level][p] + 1;
    od;
  od;
  return List([1..Length(A.base)], i -> Sublist(counts[i], A.orbits[i]));
end;


# Filtern von konjugierten faulen Elementen
# =========================================

# Beobachtung:
#   x^y in G_[b[1], .., b[n]] <==> 
#   for all k: b[k]^(y^-1) ist Fixpunkt von x

partition := function(lp, cp, b, points)
local i, x, images, sortcp;

  # x^y in G_b <==> b/y in Fixpoints(x)

  sortcp := [ ];
  for i in points do
    sortcp[i] := [ ];
  od;
  for x in cp do
    Add(sortcp[b/x[2]], x);
  od;
  images := Filtered(points, i -> IsBound(sortcp[i]));
end;


# Level-f"ur-Level Ansatz
# =======================

nextPairs := function ( G, level, pairs )
  local A, basepoint, nextpoint, np1, G1, Stab, S1, x;

  A := G.abstractStabChain;

  # Elemente aus pairs, die im Stabilisator liegen, aber nicht tiefer
Print("Gefilterte aus Stab..\n");
  basepoint := A.base[level];
  nextpoint := A.base[level+1];
  np1 := 
    Filtered(
      pairs, 
      x -> basepoint^x[2] = basepoint and nextpoint^x[2] <> nextpoint
    );

  # Ein Erzeugendensystem vom Stabilisator
Print("Erzeugendensystem von Stab..\c");
  Stab := Stabilizer(G, Sublist(A.base, [1..level-1]), OnTuples);
Print("\n");
  G1   := Subgroup(Stab, [ ]); 
  S1   := [ ];
  for x in pairs do
    if not x[2] in G1 then
Print("+\c");
      Add(S1, x);
      G1 := Closure(G1, x[2]);
    fi;
  od;

  return [np1, S1];
end;




randomlazypairs := function(G, l, h, nr)
local i, T, j, p, mp;

  i := Random([l..h]);
  T := [ ];
  for j in [1..nr] do
    p  := RandomPair(G, i);
    mp := NrMovedPointsPerm(p[2]);
    if mp < 17 then
      Print(mp," \c");
      Add(T, p);
    fi;
  od;
  return T;
end;


isconjugate := function(pair)
local lw;

  lw := LengthWord(pair[1]);
  return Subword(pair[1], 1, 1)^-1 = Subword(pair[1], lw, lw);
end;

# L"osungsbestimmung
# ==================

solutionNoFinalPart := function ( G, solutionToStatePerm ) 
  local T, x, w, basepoint, level;

  T := i -> ASCOps.TransversalOrbitGraph(G, i);
  x := solutionToStatePerm;
  w := [ ];
  for level in [1..Length(G.abstractStabChain.base)] do
    basepoint := G.abstractStabChain.base[level];
    Add(w, T(level)[basepoint^x][1]^-1);
    x := x / T(level)[basepoint^x][2];
  od;
  return w;
end;

# L"osen durch Ziel-Zittern
# =========================

# l"ose statt x, x*w f"ur kurze Worte w

tremblesolution := function ( solutionToStatePerm, listShortPairs )
  local i, x, L, solL, sol, len, sp, solL1, sol1, len1;

  x := solutionToStatePerm;
  L := listShortPairs;
  solL  := solutionNoFinalPart(x);
  sol   := Product(solL);
  len   := LengthWord(sol);
  solL1 := solL;
  Print(len, " \c");
  i := 0;
  for sp in L do
    i := i + 1;
    if i mod 100 = 0 then
      Print("#",i,"# \c");
    fi;
    solL1 := solutionNoFinalPart(x*sp[2]);
    sol1  := sp[1]*Product(solL1);
    len1 := LengthWord(sol1);
    if len1 < len then
      sol   := sp[1]^-1*sol;
      len   := len1;
      Print(len, " \c");
    fi;
  od;
  Print("\n");
  return sol;
end;

# factorInversePerm(G, inversePerm)
#   returns a list W of words such that
#     inversePerm^-1 = 
#       MappedWord(Product(W), G.abstractGenerators, G.generators).

factorInversePerm := function ( G, inversePerm )
  local A, T, perm, words, level, basepoint, representative;

  if not IsBound(G.abstractStabChain) then
    Error("<G> must have abstractStabChain");
  fi;

  A := G.abstractStabChain;
  T := level -> ASCOps.TransversalOrbitGraph(G, level);

  perm  := inversePerm^-1;
  words := [ ];
  for level in [1..Length(A.base)] do
    basepoint      := A.base[level];
    representative := T(level)[basepoint ^ perm];

    Add(words, representative[1]^-1);
    perm := perm / representative[2];    
  od;
  return words;
end;

# tremblesolution1(G, nrShortPairs, state)
#   returns a list W of words such that
#     state^-1 = MappedWord(Product(W), G.abstractGenerators, G.generators)
#   The first nrShortPairs many G.shortPairs are used to
#   reduce LengthWord(Product(W)). The first entry W[1] is a
#   short word, W[level+1] is for the given level.
#   Note, when applied to a puzzle then state is the permutation
#   which satisfies originalLayout^state = scrambledLayout.

tremblesolution1 := function ( G, nrShortPairs, state)
  local w, i, wi, si;

  w := Concatenation([ IdWord ], factorInversePerm(G, state));
  for i in [1..Minimum(nrShortPairs, Length(G.shortPairs))] do
    si := G.shortPairs[i];
    wi := Concatenation([ si[1] ], factorInversePerm(G, state * si[2]));
    if LengthWord(Product(wi)) < LengthWord(Product(w)) then
      w := wi;
    fi;
  od;
  return w;
end;

mappedWord := function (G, w)
  return MappedWord(w, G.abstractGenerators, G.generators);
end;

# L"osung mit AbStab
# ==================
#
#if not IsBound(MakeAbStabChain) then
#  Read("AbStab.g");
#
#  AbTransversals := function ( G )
#    local T;
#
#    T := [ ];
#    while IsBound(G.leftSchreier) do
#      Add(T, List(G.leftSchreier.ASchreier, t -> t^-1));
#      if IsBound(G.stabilizerSubgroup) then
#        G := G.stabilizerSubgroup;
#      else
#        return T;
#      fi;
#    od;
#    return T;
#  end;
#
#  AbOrbits := function ( G )
#    local B;
#
#    B := [ ];
#    while IsBound(G.orb) do
#      Add(B, G.orb);
#      if IsBound(G.stabilizerSubgroup) then
#        G := G.stabilizerSubgroup;
#      else
#        return B;
#      fi;
#    od;
#    return B;
#  end;
#fi;

# Neuer Ansatz: Schreier-Tripel sicher nutzen
# ===========================================

# filtere aus pairs ein Erzeugendensystem von G^(level) heraus (G^(1) := G)
filterGeneratingSet := function ( G, level, pairs )
  local A, Glevel, S, GS, x;

Print("stabilizer; \c");
  A      := G.abstractStabChain;
  Glevel := Stabilizer(G, Sublist(A.base, [1..level-1]), OnTuples);
  MakeStabChain(Glevel, A.base);
  ExtendStabChain(Glevel, A.base);
  if Size(Glevel) = 0 then
    return [ ];
  fi;

Print("subgroup; \c");
  S  := [ ];
  GS := Subgroup(Glevel, [ ]);
  MakeStabChain(Glevel, A.base);
  ExtendStabChain(Glevel, A.base);

Print("sorting; \c");
  Sort(pairs);

Print("searching; \c");
  for x in pairs do
Print(".\c");
    if x[2] in Glevel and not x[2] in GS then
      Add(S, x);
      GS := Closure(GS, x[2]);
      if Size(GS) = Size(Glevel) then
        return S;
      fi;
    fi;
  od;
  Print("#I set of pairs did not contain generating set\n");
  return S;
end;

# Suche aus A.quotients[level-1] den k"urzesten neuen Quotienten x/y
# heraus, der in G^(level) liegt und A.base[level] -> basepointImage
# abbildet:
#   Geg. G, b1, b2, c2, suche x/y in G_b1 mit b2^(x/y) = c2.
#   Offensichtlich gilt 
#     (1) x/y in G_b1 <==> b1^x = b1^y und
#     (2) b2^(x/y) = c2 <==> b2^x = c2^y.

fitQuotient := function ( G, level, basepointImage )
  local A, basepoint, q, p, X, bX, x, y, yx;

  A         := G.abstractStabChain;
  basepoint := A.base[level];

  q := false;
  for p in A.quotients[level-1].points do
    X := 
      Concatenation(
        A.quotients[level-1].new[p], 
        A.quotients[level-1].used[p]
      );
    bX := Set(List(X, x -> basepoint^x[2]));
    for x in X do
      if basepointImage^x[2] in bX then
        for y in X do
          if basepoint^y[2] = basepointImage^x[2] then
            yx := [ y[1]/x[1], y[2]/x[2] ];
            if q = false or yx < q then
              q := yx;
            fi;
          fi;
        od;
      fi;
    od;
  od;
  return q;
end;

basepointImageHoles := function ( G, level )
  local A, T;

  A := G.abstractStabChain;
  T := ASCOps.TransversalOrbitGraph(G, level);
  return Filtered(A.orbits[level], p -> not IsBound(T[p]));
end;
