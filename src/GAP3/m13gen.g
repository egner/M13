# M12 f"ur M13, SE, 7.8.96, GAP v3.4

# der Zustand (Kodierung wie in M13.java)
initialState :=
  [12, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

find_k := function ( state, c )
  local k;

  for k in [0, 2 .. 24] do
    if state[1+k/2] = c then
      return k;
    fi;
  od;
  return false;
end;

# im Zustand state den Stein c ziehen
move := function ( state, c )
  local kc, kHole, ka, kb, k, kL, statec, d;
 
  kc    := find_k(state, c);
  kHole := find_k(state, 12);

  kL := 1;
  while (
    (kL < 26) and
    not (
      ( (kL +  1) mod 26 = kc or
        (kL +  9) mod 26 = kc or
        (kL + 21) mod 26 = kc or
        (kL + 25) mod 26 = kc 
      ) and
      ( (kL +  1) mod 26 = kHole or
        (kL +  9) mod 26 = kHole or
        (kL + 21) mod 26 = kHole or
        (kL + 25) mod 26 = kHole
      )
    )
  ) do
    kL := kL + 2;
  od;
  
  ka := false;
  kb := false;
  for d in [1, 9, 21, 25] do
    k := (kL + d) mod 26;
    if (k <> kc) and (k <> kHole) then
      if ka = false then
        ka := k;
      else
        kb := k;
      fi;
    fi;
  od;

  statec := ShallowCopy(state);
  statec[1+kc/2]    := state[1+kHole/2];
  statec[1+kHole/2] := state[1+kc/2];
  statec[1+ka/2]    := state[1+kb/2];
  statec[1+kb/2]    := state[1+ka/2];

  return statec;
end;

# konstruiere die Dreiecksz"uge
triangleMoves := function ( )
  local m, a, b, s;

  m := [ ];
  for a in [0..11] do
    for b in [0..11] do
      s := move(move(move(initialState, a), b), a);
      if b <> a and s[1] = 12 then
        s := PermList(List(s, si -> Position(initialState, si)));
        if not ForAny(m, mi -> mi[1] = s) then
   	  Add(m, [s, [a, b, a]]);
        fi;
      fi;
    od;
  od;
  return m;
end;
triangleMoves := triangleMoves();
# ==> 54 Erzeuger der Form aba aus dem Stabilisator des Lochs

# baue die Gruppe
M12 := Group(List(triangleMoves, x -> x[1]), ());
M12.abstractGenerators :=
  List([1..Length(triangleMoves)], 
    i -> AbstractGenerator(ConcatenationString("g[", String(i), "]"))
  );
M12.triangleMoves := 
  List(
    triangleMoves,
    x -> [ x[2][1]+1, x[2][2]+1, 12 ]
  );

# baue eine AbstractStabChain
# ---------------------------
#
# Read("abstabch.g");
# AbstractStabChainGenerationAllStrategies(M12, 10000, []);
# PrintASCToC("m12.sgs", M12);
# # output M12.triangleMoves into int triangleMoves[][];
