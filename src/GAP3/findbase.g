# Tools f"ur Stabilisatorketten
# MP, SE, 14.- 31.10.96
# MP, SE, 4.2.97 bugfix
# MP, 10.03.97 S"auberung


# Das Rohmaterial zur Basisfindung
# ================================

#F movedPointsSet( <permgroup> )
#F   computes the set of all sets of moved points for 
#F     (lazy pairs)^(short pairs).
#F   The function calculates an ordered list of pairs 
#F   [ smallestWord, movedPoints ], assigning it to 
#F   G.movedPointsList.
#F

movedPointsSets := function ( G )
  local 
    lp,       # pairs [smallestWord, movedPoints] built from G.lazyPairs
    lp1,      # temporary lp
    l, s, l1, # pointer
    mp,       # pairs [smallestWord, movedPoints] built from 
              # G.lazyPairs^G.shortPairs
    mp1, mp2, # temporary mp
    m, m1,    # pointer
    i, i1, j; # counter

  # prepare short and lazy pairs
  if not IsBound(G.shortPairs) then
    EnumeratePermGroup(G);
  fi;
  if not IsBound(G.lazyPairs) then
    MakeLazyPairs(G);
  fi;

  # build set of moved point sets from G.lazyPairs
  # (extended as [mp, word]);
  # start with the generating set of G
  lp :=
    List(
      [1..Length(G.generators)], 
      k -> 
        [ MovedPointsPerm(G.generators[k]), 
          G.abstractGenerators[k] 
        ]
    ); 
  for l in G.lazyPairs do
    Add(lp, [ MovedPointsPerm(l[2]), l[1] ]);
  od;

  # collect shortest word for every moved point set
  Sort(lp);
  l1  := lp[1];
  lp1 := [ ];
  for l in lp do
    if l[1] <> l1[1] then
      Add(lp1, l1);
      l1 := l;
    fi;
  od;
  Add(lp1, l1);
  lp := lp1;

  Print("#I |{ mp(l) | l in G.lazyPairs }| = ", Length(lp), "\n");
  Print("#I |G.shortPairs|                 = ", Length(G.shortPairs), "\n");

  # construct all the conjugated moved point sets
  mp := [ ];

  for l in lp do

    if Position(lp, l) mod 100 = 0 then
      Print("\n***",Position(lp, l),"***\n");
    fi;
    mp1 := [ ];
    for s in G.shortPairs do
      Add(mp1, [ OnSets(l[1], s[2]), l[2]^s[1] ]);
    od;

    # collect shortest word
    Sort(mp1);
    m1  := mp1[1];
    mp2 := [ ];
    for m in mp1 do
      if m[1] <> m1[1] then
        Add(mp2, m1);
        m1 := m;
      fi;
    od;
    Add(mp2, m1);
    mp1 := mp2;

    # merge mp and mp1 
    mp2 := [ ];
    i   := 1;
    i1  := 1;
    while i <= Length(mp) and i1 <= Length(mp1) do
      if mp[i][1] < mp1[i1][1] then
        Add(mp2, mp[i]);
        i := i + 1;
      elif mp[i][1] > mp1[i1][1] then
        Add(mp2, mp1[i1]);
        i1 := i1 + 1;
      else  # mp[i][1] = mp1[i1][1]
        Add(mp2, Minimum([mp[i], mp1[i1]]));
        i  := i + 1;
        i1 := i1 + 1;
      fi;
    od;
    if i <= Length(mp) then
      for j in [i..Length(mp)] do
     Add(mp2, mp[j]);
      od;
    fi;
    if i1 <= Length(mp1) then
      for j in [i1..Length(mp1)] do
     Add(mp2, mp1[j]);
      od;
    fi;

    mp := mp2;
    Print(Length(mp), " \c");

  od; # for l in lp

  Print("\n");

  # sort by the wordlength
  Print("#I sorting by length of word\n");
  for m in mp do
    m1   := m[1];
    m[1] := m[2];
    m[2] := m1;
  od;
  Sort(mp);
  G.movedPointsList := mp;
end;


# Basisfindung
# ============

#F findbaseinitial( <permgroup>, <maxwordlength>, <final-part-of-base> )
#F   calculates a list of pairs [word, extra moved points] with words
#F   in G.movedPointsList of length <= maxwordlength with 
#F   the method "ascent with smallest steps", such that the 
#F   corresponding base has final-part-of-base as deepest part.
#F   

# The method "ascent with smallest steps" does the following:
# If the base to be created already consists of the points
# B = {i_1,..,i_r}, then elements of G.movedPointsList are considered, 
# which move a minimal number of points not in B (but more than 0) 
# and among all those the one with the shortest corresponding word 
# is chosen. 
# Then B is extended by those extra moved points and the baselist
# to be returned is extended by the pair [word, extra moved points].
# Concatenation of the extra moved points yields a base.
# The words in B are intended to serve as a kind of "seed" in the 
# abstract stabchain to be computed later. 

findbaseinitial := function ( G, maxwordlength, finalpartofbase )
  local 
    mp,        # list of [nr of extra moved points, word, moved points set]
    max,       # maximal word length considered
    fin,       # final part of base
    mp1,       # temporary mp
    i,         # counter
    t,         # triples in mp
    len, len1, # temporaries
    min,       # Minimum(mp) = next element in baselist
    baselist,  # baselist to be returned
    points,    # points already treated in the baselist
    allpoints; # moved points of Gmin

  if not IsBound(G.movedPointsList) then
    Error("G.movedPointsList is not present");
  fi;

  mp        := ShallowCopy(G.movedPointsList);
  max       := maxwordlength;
  fin       := finalpartofbase;
  allpoints := PermGroupOps.MovedPoints(G);

  # Extract the part of G.movedPointsList with the 
  # following properties:
  #   1. the length of the word is <= max
  #   2. the moved points set contains points not in fin
  # and construct a list of triples
  #   [ nr of extra moved points, word, moved points set ].
  # Note that the first condition characterizes an initial 
  # part of G.movedPointsList.
  Print("#I extending\n");
  mp1 := [ ];
  i   := 1;
  len := Length(mp);
  while i <= len and LengthWord(mp[i][1]) <= max do
    if not IsSubset(fin, mp[i][2]) then
      Add(
        mp1, 
        [ Length(Difference(mp[i][2], fin)), 
          mp[i][1], 
          mp[i][2]
        ]
      );
    fi;
    i := i + 1;
  od;
  mp := mp1;

  # construct baselist with "small steps"
  baselist  := [ ];
  points    := fin;
  if Length(fin) > 0 then
    Add(baselist, ["finalpart", fin]);
  fi;
  while (Length(mp) > 0 and points <> allpoints) do
    Print(Length(mp), " \c");
    min := Minimum(mp);
    Add(baselist, [min[2], Difference(min[3], points)]);
    points := Union(points, min[3]);

    # actualize mp
    mp1 := [ ];
    for t in mp do
      len1 := Length(Difference(t[3], points));
      if len1 > 0 then
        Add(mp1, [len1, t[2], t[3]]);
      fi;
    od;
    mp := mp1;
  od;  
  Print("\n");

  return baselist;
end;


# Basisverfeinerung
# =================

#F refinebase( <permgroup> , <baselist> , <range-of-int> )
#F   refines baselist (a list of pairs [word, extramovedpoints])
#F   by using elements of G.movedPointsList of wordlength specified
#F   by the third argument which should be a range. The wordlengths
#F   used for refinement should be greater than those in the baselist.
#F

refinebase := function ( G, baselist, wordlengths )
  local 
    b,           # calculated to be maximal wordlength in baselist
    len,         # wordlength
    L,           # temporary list constructed of baselist
    low, high,   # first and last index of the part of
                 # G.movedPointsList to be considered
    allpoints,   # moved points of G
    x, j,        # temporaries
    mp,          # candidates for refinement
    cp,          # partition of mp according to baselist
    points,      # upper and
    oldpoints,   # lower bound for points considered for refinement
    p,           # element of baselist
    pos,         # position of p in baselist
    newbaselist, # refined baselist to be returned
    pts, i1, i,  # temporaries
    min,         # best element for refinement
    diff, diff1, # difference of pointsets considered during 
                 # search for best refiner
    m;           # temporary

  # check arguments
  if not IsPermGroup(G) then
    Error(
      "usage: refinebase( <permgroup> , <baselist> , <range-of-int> )"
    );
  fi;
  if not IsList(baselist) then
    Error(
      "usage: refinebase( <permgroup> ,<baselist> , <range-of-int> )"
    );
  fi;
  if not IsRange(wordlengths) then
    Error(
      "usage: refinebase( <permgroup> ,<baselist> ,<range-of-int> )"
    );
  fi;  

  # calculate maximal wordlength occuring in baselist
  b := 1;
  j := 1;
  if baselist[1][1] = "finalpart" then
    j := j + 1;
  fi;
  for i in [j..Length(baselist)] do
    len := LengthWord(baselist[i][1]);
    if len > b then
      b := len; 
    fi;
  od;

  # check if words for refinement are longer than
  # those in baselist
  if wordlengths[1] <= b then
    Error("words of length ",b," are already considered in baselist");
  fi;


  # check if G.movedPointsList is present
  if not IsBound(G.movedPointsList) then
    Error("G.movedPointsList is not present");
  fi;

  # check if refinement is possible
  if ForAll(baselist, p -> p[1] = "finalpart" or Length(p[2]) = 1) then
    Print("#I baselist is maximal refined \n");
    return baselist;
  fi;

  # get actual base and check if length is correct
  allpoints := Union(List(baselist, x -> x[2]));
  if Set(allpoints) <> Set(PermGroupOps.MovedPoints(G)) then
    Error("moved points of G are missing in baselist");
  fi;

  # determine part of G.movedPointsList which must 
  # be considered
  low  := 
    PositionProperty(
      G.movedPointsList, 
      p -> LengthWord(p[1]) >= wordlengths[1]
    );
  high := 
    PositionProperty(
      G.movedPointsList, 
      p -> LengthWord(p[1]) > wordlengths[Length(wordlengths)]
    );
  if low = false then
    return baselist;
  fi;
  if high = false then
    high := Length(G.movedPointsList) + 1;
  fi;

  # extract relevant part of G.movedPointsList and
  # add baselist (extended to pairs  [word, movedpoints])
  # in front
  L := [ ];
  if baselist[1][1] <> "finalpart" then  # finalpart present?
    Add(L, baselist[1]);
  fi;
  for i in [2.. Length(baselist)] do
    Add(
      L, 
      [baselist[i][1], Union(List([1..i], j -> baselist[j][2]))]
    );
  od;
  mp := 
    Concatenation(
      L, 
      Sublist(G.movedPointsList, [low..high-1])
    );
  Print("#I number of candidates for refinement: ",high - low,"\n");

  # partition mp according to baselist, what means:
  # let p in mp, then p in cp[i] <==> 
  #   p[2] is contained in baselist[i][2], but not in baselist[i + 1][2].
  # Note that all cp[i]'s are not empty since baselist[i] is contained.
  cp := List(baselist, p -> [ ]);
  for x in mp do
    i   := 1;
    pts := baselist[1][2];
    while not IsSubset(pts, x[2]) do
      i   := i + 1;
      pts := Union(pts, baselist[i][2]);
    od;
    Add(cp[i], x);
  od;

  # refine
  points      := [ ];
  oldpoints   := [ ];
  newbaselist := [ ];
  for p in baselist do
    pos    := Position(baselist, p);
    points := Union(points, p[2]);
    if Length(p[2]) = 1 or p[1] = "finalpart" then   # refinement impossible
      Add(newbaselist, p);                           # resp. not necessary
      oldpoints := points;
    else
      while oldpoints <> points do
    i1 := 
      PositionProperty(
        cp[pos], 
        p -> Length(Difference(p[2], oldpoints)) > 0
      );
    if i1 = false then
      return "geht nicht";
    fi;
    min := cp[pos][i1];
    diff := Difference(cp[pos][1][2], oldpoints);
    for i in [i1+1..Length(cp[pos])] do
      m     := cp[pos][i];
      diff1 := Difference(m[2], oldpoints);
      if Length(diff1) > 0 and Length(diff1) <= Length(diff) then
        if [Length(diff1), m] < [Length(diff), min] then
          min  := m;
          diff := diff1;
        fi;
      fi;
    od;
    Add(newbaselist, [min[1], diff]);
    oldpoints := Union(oldpoints, diff);
      od;
    fi;
  od; # for p in baselist

  # print informations
  Print("#I length of baselist = ",Length(newbaselist)," \c");

  # check if baselist is maximal refined
  if ForAll(newbaselist, p -> p[1] = "finalpart" or Length(p[2]) = 1) then
    Print("#I baselist is maximal refined");
  fi;
  Print("\n");

  return newbaselist;

  end;


# Makros f"ur Basisfindung und Verfeinerung
# =======================================

# Da die Verfeinerung einer bestehenden baselist immer sinnvoll
# ist, da sie im schlechtesten Falle gleich bleibt, bietet sich
# folgende Vorgehensweise an:
#   1. Berechne eine erste baselist mit W"ortern bis zur
#      L"ange m durch 
#        baselist = findbaseinitial(G, m, finalpartofbase).
#   2. Verfeinere Schrittweise die so erzeugte baselist durch
#        baselist = refinebase(G, baselist, [i]),
#      wobei i in [m + 1..l"angstes Wort in G.movedPointsList].
# Dieser Algorithmus repr"asentiert eine Strategie zur 
# Basisfindung, welche nur von m abh"angt.

#F findbase( <permgroup> , <maxwordlength> , <final-part-of-base> ) 
#F   calculates first a baselist with words of length <= maxwordlength 
#F   and final-part-of-base as deepest part of the corresponding base 
#F   and then refines stepwise as far as possible.
#F

findbase := function ( G, m, finalpartofbase )
  local 
    L,   # baselist to be returned
    max, # maximal wordlength occuring in G.movedPointsList
    j;   # counter

  Print("#I calculating initial baselist with words of length <= ",m,"\n");
  L := findbaseinitial(G, m, finalpartofbase);
  Print("#I length of baselist = ",Length(L),"\n");
  max := LengthWord(G.movedPointsList[Length(G.movedPointsList)][1]);
  Print("#I refining baselist\n");
  for j in [m + 1..max] do
    L := refinebase(G, L, [j]);
  od;

  return L;
  
end;


#F findbaseall( <permgroup> , <final-part-of-base> )
#F   calculates baselists with all strategies i, 
#F   1 <= i <= LengthWord(longest word in G.movedPointsList). 
#F   Strategy i means calculating an initial baselist with 
#F   words of length <= i (findbaseinitial) and stepwise refinement 
#F   (refinebase) afterwards. If the calculation of the initial 
#F   baselist already produces a maximal refined baselist then further 
#F   strategies are suppressed, because they will produce nothing new.
#F

findbaseall := function( G, finalpartofbase )
  local max, L, bl, stop, mp, max, j, i;

  max  := LengthWord(G.movedPointsList[Length(G.movedPointsList)][1]);
  L    := [ ];
  i    := 1;
  stop := false;
  while i <= max and not stop do

    # information
    Print("strategy ",i,"\n");
    Print("-----------\n\n");
    Print("#I calculating initial baselist with words of length <= ",i,"\n");

    # calculating initial baselist
    bl := findbaseinitial(G, i, finalpartofbase);
    # if the initial baselist is already maximal refined then 
    # further calculation will reproduce always the same baselists
    if 
      bl <> [] and 
      ForAll(bl, p -> p[1] = "finalpart" or Length(p[2]) = 1) 
    then
      stop := true;
    fi;
    Print("#I length of baselist = ",Length(bl),"\n");
    mp  := G.movedPointsList;
    max := LengthWord(mp[Length(mp)][1]);
    Print("#I refining baselist\n");

    # stepwise refinement of baselist
    for j in [i+1..max] do
      bl := refinebase(G, bl, [j]);
    od;
    Add(L, bl);
    i := i + 1;
    Print("\n");
  od;

  # information
  if i < max then
    Print(
      "#I strategies ",i," - ",max," will produce the same result like strategy ",i-1,"\n");
  fi; 

  return L;
end;

